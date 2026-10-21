// Printed from the Lean programs in SszNative by `just lean-kernels`.
// Do not edit: the regressions fail when this file differs from what they print.
#if defined(__x86_64__) && !defined(_WIN32)
#if defined(__APPLE__)
#define SYMBOL(name) _##name
#else
#define SYMBOL(name) name
#endif
	.intel_syntax noprefix
	.text
	.globl SYMBOL(ssz_sha256_avx512_pairs)
	.p2align 6
SYMBOL(ssz_sha256_avx512_pairs):
	test rcx, rcx
	jz .Lssz_sha256_avx512_pairs_3111
.Lssz_sha256_avx512_pairs_2:
	vmovdqu ymm8, ymmword ptr [rsi + 0]
	vmovdqu32 ymm16, ymmword ptr [rdx + 0]
	vmovdqu ymm9, ymmword ptr [rsi + 64]
	vmovdqu32 ymm17, ymmword ptr [rdx + 64]
	vmovdqu ymm10, ymmword ptr [rsi + 128]
	vmovdqu32 ymm18, ymmword ptr [rdx + 128]
	vmovdqu ymm11, ymmword ptr [rsi + 192]
	vmovdqu32 ymm19, ymmword ptr [rdx + 192]
	vmovdqu ymm12, ymmword ptr [rsi + 256]
	vmovdqu32 ymm20, ymmword ptr [rdx + 256]
	vmovdqu ymm13, ymmword ptr [rsi + 320]
	vmovdqu32 ymm21, ymmword ptr [rdx + 320]
	vmovdqu ymm14, ymmword ptr [rsi + 384]
	vmovdqu32 ymm22, ymmword ptr [rdx + 384]
	vmovdqu ymm15, ymmword ptr [rsi + 448]
	vmovdqu32 ymm23, ymmword ptr [rdx + 448]
	vinserti64x4 zmm8, zmm8, ymmword ptr [rsi + 512], 1
	vinserti64x4 zmm16, zmm16, ymmword ptr [rdx + 512], 1
	vinserti64x4 zmm9, zmm9, ymmword ptr [rsi + 576], 1
	vinserti64x4 zmm17, zmm17, ymmword ptr [rdx + 576], 1
	vinserti64x4 zmm10, zmm10, ymmword ptr [rsi + 640], 1
	vinserti64x4 zmm18, zmm18, ymmword ptr [rdx + 640], 1
	vinserti64x4 zmm11, zmm11, ymmword ptr [rsi + 704], 1
	vinserti64x4 zmm19, zmm19, ymmword ptr [rdx + 704], 1
	vinserti64x4 zmm12, zmm12, ymmword ptr [rsi + 768], 1
	vinserti64x4 zmm20, zmm20, ymmword ptr [rdx + 768], 1
	vinserti64x4 zmm13, zmm13, ymmword ptr [rsi + 832], 1
	vinserti64x4 zmm21, zmm21, ymmword ptr [rdx + 832], 1
	vinserti64x4 zmm14, zmm14, ymmword ptr [rsi + 896], 1
	vinserti64x4 zmm22, zmm22, ymmword ptr [rdx + 896], 1
	vinserti64x4 zmm15, zmm15, ymmword ptr [rsi + 960], 1
	vinserti64x4 zmm23, zmm23, ymmword ptr [rdx + 960], 1
	vshufps zmm25, zmm8, zmm9, 0x44
	vshufps zmm8, zmm8, zmm9, 0xee
	vshufps zmm26, zmm10, zmm11, 0x44
	vshufps zmm10, zmm10, zmm11, 0xee
	vshufps zmm11, zmm25, zmm26, 0xdd
	vshufps zmm9, zmm8, zmm10, 0x88
	vshufps zmm8, zmm8, zmm10, 0xdd
	vshufps zmm25, zmm25, zmm26, 0x88
	vmovdqu32 zmm29, zmmword ptr [r8 + 8768]
	vmovdqu32 zmm30, zmmword ptr [r8 + 8832]
	vshufps zmm10, zmm12, zmm13, 0x44
	vshufps zmm12, zmm12, zmm13, 0xee
	vshufps zmm26, zmm14, zmm15, 0x44
	vshufps zmm14, zmm14, zmm15, 0xee
	vshufps zmm15, zmm10, zmm26, 0xdd
	vshufps zmm13, zmm12, zmm14, 0x88
	vshufps zmm12, zmm12, zmm14, 0xdd
	vshufps zmm10, zmm10, zmm26, 0x88
	vshufps zmm14, zmm16, zmm17, 0x44
	vshufps zmm16, zmm16, zmm17, 0xee
	vshufps zmm26, zmm18, zmm19, 0x44
	vshufps zmm18, zmm18, zmm19, 0xee
	vshufps zmm19, zmm14, zmm26, 0xdd
	vshufps zmm17, zmm16, zmm18, 0x88
	vshufps zmm16, zmm16, zmm18, 0xdd
	vshufps zmm14, zmm14, zmm26, 0x88
	vshufps zmm18, zmm20, zmm21, 0x44
	vshufps zmm20, zmm20, zmm21, 0xee
	vshufps zmm26, zmm22, zmm23, 0x44
	vshufps zmm22, zmm22, zmm23, 0xee
	vshufps zmm23, zmm18, zmm26, 0xdd
	vshufps zmm21, zmm20, zmm22, 0x88
	vshufps zmm20, zmm20, zmm22, 0xdd
	vshufps zmm18, zmm18, zmm26, 0x88
	vmovdqa32 zmm26, zmm29
	vpermi2q zmm26, zmm17, zmm21
	vmovdqa32 zmm22, zmm30
	vpermi2q zmm22, zmm17, zmm21
	vmovdqa32 zmm17, zmm29
	vpermi2q zmm17, zmm19, zmm23
	vmovdqa32 zmm21, zmm30
	vpermi2q zmm21, zmm19, zmm23
	vmovdqa32 zmm19, zmm29
	vpermi2q zmm19, zmm16, zmm20
	vmovdqa32 zmm23, zmm30
	vpermi2q zmm23, zmm16, zmm20
	vmovdqa32 zmm16, zmm29
	vpermi2q zmm16, zmm14, zmm18
	vmovdqa32 zmm20, zmm30
	vpermi2q zmm20, zmm14, zmm18
	vmovdqa32 zmm18, zmm26
	vmovdqa32 zmm26, zmm29
	vpermi2q zmm26, zmm9, zmm13
	vmovdqa32 zmm14, zmm30
	vpermi2q zmm14, zmm9, zmm13
	vmovdqa32 zmm9, zmm29
	vpermi2q zmm9, zmm11, zmm15
	vmovdqa32 zmm13, zmm30
	vpermi2q zmm13, zmm11, zmm15
	vmovdqa32 zmm11, zmm29
	vpermi2q zmm11, zmm8, zmm12
	vmovdqa32 zmm15, zmm30
	vpermi2q zmm15, zmm8, zmm12
	vmovdqa32 zmm8, zmm29
	vpermi2q zmm8, zmm25, zmm10
	vmovdqa32 zmm12, zmm30
	vpermi2q zmm12, zmm25, zmm10
	vmovdqa32 zmm10, zmm26
	vmovdqu32 zmm27, zmmword ptr [r8 + 8704]
	vpshufb zmm8, zmm8, zmm27
	vpshufb zmm9, zmm9, zmm27
	vpshufb zmm10, zmm10, zmm27
	vpshufb zmm11, zmm11, zmm27
	vpshufb zmm12, zmm12, zmm27
	vpshufb zmm13, zmm13, zmm27
	vpshufb zmm14, zmm14, zmm27
	vpshufb zmm15, zmm15, zmm27
	vpshufb zmm16, zmm16, zmm27
	vpshufb zmm17, zmm17, zmm27
	vpshufb zmm18, zmm18, zmm27
	vpshufb zmm19, zmm19, zmm27
	vpshufb zmm20, zmm20, zmm27
	vpshufb zmm21, zmm21, zmm27
	vpshufb zmm22, zmm22, zmm27
	vpshufb zmm23, zmm23, zmm27
	vmovdqu32 zmm0, zmmword ptr [r8 + 8192]
	vmovdqu32 zmm1, zmmword ptr [r8 + 8256]
	vmovdqu32 zmm2, zmmword ptr [r8 + 8320]
	vmovdqu32 zmm3, zmmword ptr [r8 + 8384]
	vmovdqu32 zmm4, zmmword ptr [r8 + 8448]
	vmovdqu32 zmm5, zmmword ptr [r8 + 8512]
	vmovdqu32 zmm6, zmmword ptr [r8 + 8576]
	vmovdqu32 zmm7, zmmword ptr [r8 + 8640]
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 0]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 64]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 128]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 192]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 256]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 320]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 384]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 448]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 512]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 576]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 640]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 704]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 768]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 832]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 896]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 960]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 1024]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 1088]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 1152]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 1216]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 1280]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 1344]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 1408]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 1472]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 1536]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 1600]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 1664]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 1728]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 1792]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 1856]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 1920]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 1984]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 2048]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 2112]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 2176]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 2240]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 2304]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 2368]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 2432]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 2496]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 2560]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 2624]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 2688]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 2752]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 2816]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 2880]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 2944]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 3008]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 3072]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 3136]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 3200]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 3264]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 3328]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 3392]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 3456]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 3520]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 3584]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 3648]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 3712]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 3776]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 3840]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 3904]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 3968]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 4032]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm0, zmm0, zmmword ptr [r8 + 8192]
	vmovdqa32 zmm8, zmm0
	vpaddd zmm1, zmm1, zmmword ptr [r8 + 8256]
	vmovdqa32 zmm9, zmm1
	vpaddd zmm2, zmm2, zmmword ptr [r8 + 8320]
	vmovdqa32 zmm10, zmm2
	vpaddd zmm3, zmm3, zmmword ptr [r8 + 8384]
	vmovdqa32 zmm11, zmm3
	vpaddd zmm4, zmm4, zmmword ptr [r8 + 8448]
	vmovdqa32 zmm12, zmm4
	vpaddd zmm5, zmm5, zmmword ptr [r8 + 8512]
	vmovdqa32 zmm13, zmm5
	vpaddd zmm6, zmm6, zmmword ptr [r8 + 8576]
	vmovdqa32 zmm14, zmm6
	vpaddd zmm7, zmm7, zmmword ptr [r8 + 8640]
	vmovdqa32 zmm15, zmm7
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 4096]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 4160]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 4224]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 4288]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 4352]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 4416]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 4480]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 4544]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 4608]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 4672]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 4736]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 4800]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 4864]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 4928]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 4992]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 5056]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 5120]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 5184]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 5248]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 5312]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 5376]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 5440]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 5504]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 5568]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 5632]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 5696]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 5760]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 5824]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 5888]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 5952]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 6016]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 6080]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 6144]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 6208]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 6272]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 6336]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 6400]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 6464]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 6528]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 6592]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 6656]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 6720]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 6784]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 6848]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 6912]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 6976]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 7040]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 7104]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 7168]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 7232]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 7296]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 7360]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 7424]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 7488]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 7552]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 7616]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 7680]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 7744]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 7808]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 7872]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 7936]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 8000]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 8064]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 8128]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm0, zmm0, zmm8
	vpaddd zmm1, zmm1, zmm9
	vpaddd zmm2, zmm2, zmm10
	vpaddd zmm3, zmm3, zmm11
	vpaddd zmm4, zmm4, zmm12
	vpaddd zmm5, zmm5, zmm13
	vpaddd zmm6, zmm6, zmm14
	vpaddd zmm7, zmm7, zmm15
	vmovdqu32 zmm30, zmmword ptr [r8 + 8896]
	vmovdqu32 zmm31, zmmword ptr [r8 + 8960]
	vmovdqa32 zmm25, zmm30
	vmovdqa32 zmm26, zmm30
	vpermi2d zmm25, zmm0, zmm4
	vpermi2d zmm26, zmm1, zmm5
	vmovdqa32 zmm27, zmm31
	vmovdqa32 zmm28, zmm31
	vpermi2d zmm27, zmm0, zmm4
	vpermi2d zmm28, zmm1, zmm5
	vmovdqa32 zmm0, zmm30
	vmovdqa32 zmm1, zmm30
	vpermi2d zmm0, zmm2, zmm6
	vpermi2d zmm1, zmm3, zmm7
	vmovdqa32 zmm4, zmm31
	vmovdqa32 zmm5, zmm31
	vpermi2d zmm4, zmm2, zmm6
	vpermi2d zmm5, zmm3, zmm7
	vshufps zmm6, zmm25, zmm26, 0x88
	vshufps zmm7, zmm25, zmm26, 0xdd
	vshufps zmm26, zmm27, zmm28, 0x88
	vshufps zmm25, zmm27, zmm28, 0xdd
	vshufps zmm27, zmm4, zmm5, 0x88
	vshufps zmm28, zmm4, zmm5, 0xdd
	vshufps zmm4, zmm0, zmm1, 0x88
	vshufps zmm5, zmm0, zmm1, 0xdd
	vmovdqa32 zmm0, zmm30
	vmovdqa32 zmm1, zmm30
	vpermi2d zmm0, zmm6, zmm4
	vpermi2d zmm1, zmm7, zmm5
	vmovdqa32 zmm2, zmm31
	vmovdqa32 zmm3, zmm31
	vpermi2d zmm2, zmm6, zmm4
	vpermi2d zmm3, zmm7, zmm5
	vmovdqa32 zmm4, zmm30
	vmovdqa32 zmm5, zmm30
	vpermi2d zmm4, zmm26, zmm27
	vpermi2d zmm5, zmm25, zmm28
	vmovdqa32 zmm6, zmm31
	vmovdqa32 zmm7, zmm31
	vpermi2d zmm6, zmm26, zmm27
	vpermi2d zmm7, zmm25, zmm28
	vmovdqu32 zmm27, zmmword ptr [r8 + 8704]
	vpshufb zmm0, zmm0, zmm27
	vmovdqu32 zmmword ptr [rdi + 0], zmm0
	vpshufb zmm1, zmm1, zmm27
	vmovdqu32 zmmword ptr [rdi + 64], zmm1
	vpshufb zmm2, zmm2, zmm27
	vmovdqu32 zmmword ptr [rdi + 128], zmm2
	vpshufb zmm3, zmm3, zmm27
	vmovdqu32 zmmword ptr [rdi + 192], zmm3
	vpshufb zmm4, zmm4, zmm27
	vmovdqu32 zmmword ptr [rdi + 256], zmm4
	vpshufb zmm5, zmm5, zmm27
	vmovdqu32 zmmword ptr [rdi + 320], zmm5
	vpshufb zmm6, zmm6, zmm27
	vmovdqu32 zmmword ptr [rdi + 384], zmm6
	vpshufb zmm7, zmm7, zmm27
	vmovdqu32 zmmword ptr [rdi + 448], zmm7
	add rsi, 1024
	add rdx, 1024
	add rdi, 512
	sub rcx, 1
	jnz .Lssz_sha256_avx512_pairs_2
.Lssz_sha256_avx512_pairs_3111:
	vzeroupper
	ret
	.globl SYMBOL(ssz_sha256_avx512_columns)
	.p2align 6
SYMBOL(ssz_sha256_avx512_columns):
	test rcx, rcx
	jz .Lssz_sha256_avx512_columns_3111
.Lssz_sha256_avx512_columns_2:
	vmovdqu ymm8, ymmword ptr [rsi + 0]
	vmovdqu32 ymm16, ymmword ptr [rdx + 0]
	vmovdqu ymm9, ymmword ptr [rsi + 32]
	vmovdqu32 ymm17, ymmword ptr [rdx + 32]
	vmovdqu ymm10, ymmword ptr [rsi + 64]
	vmovdqu32 ymm18, ymmword ptr [rdx + 64]
	vmovdqu ymm11, ymmword ptr [rsi + 96]
	vmovdqu32 ymm19, ymmword ptr [rdx + 96]
	vmovdqu ymm12, ymmword ptr [rsi + 128]
	vmovdqu32 ymm20, ymmword ptr [rdx + 128]
	vmovdqu ymm13, ymmword ptr [rsi + 160]
	vmovdqu32 ymm21, ymmword ptr [rdx + 160]
	vmovdqu ymm14, ymmword ptr [rsi + 192]
	vmovdqu32 ymm22, ymmword ptr [rdx + 192]
	vmovdqu ymm15, ymmword ptr [rsi + 224]
	vmovdqu32 ymm23, ymmword ptr [rdx + 224]
	vinserti64x4 zmm8, zmm8, ymmword ptr [rsi + 256], 1
	vinserti64x4 zmm16, zmm16, ymmword ptr [rdx + 256], 1
	vinserti64x4 zmm9, zmm9, ymmword ptr [rsi + 288], 1
	vinserti64x4 zmm17, zmm17, ymmword ptr [rdx + 288], 1
	vinserti64x4 zmm10, zmm10, ymmword ptr [rsi + 320], 1
	vinserti64x4 zmm18, zmm18, ymmword ptr [rdx + 320], 1
	vinserti64x4 zmm11, zmm11, ymmword ptr [rsi + 352], 1
	vinserti64x4 zmm19, zmm19, ymmword ptr [rdx + 352], 1
	vinserti64x4 zmm12, zmm12, ymmword ptr [rsi + 384], 1
	vinserti64x4 zmm20, zmm20, ymmword ptr [rdx + 384], 1
	vinserti64x4 zmm13, zmm13, ymmword ptr [rsi + 416], 1
	vinserti64x4 zmm21, zmm21, ymmword ptr [rdx + 416], 1
	vinserti64x4 zmm14, zmm14, ymmword ptr [rsi + 448], 1
	vinserti64x4 zmm22, zmm22, ymmword ptr [rdx + 448], 1
	vinserti64x4 zmm15, zmm15, ymmword ptr [rsi + 480], 1
	vinserti64x4 zmm23, zmm23, ymmword ptr [rdx + 480], 1
	vshufps zmm25, zmm8, zmm9, 0x44
	vshufps zmm8, zmm8, zmm9, 0xee
	vshufps zmm26, zmm10, zmm11, 0x44
	vshufps zmm10, zmm10, zmm11, 0xee
	vshufps zmm11, zmm25, zmm26, 0xdd
	vshufps zmm9, zmm8, zmm10, 0x88
	vshufps zmm8, zmm8, zmm10, 0xdd
	vshufps zmm25, zmm25, zmm26, 0x88
	vmovdqu32 zmm29, zmmword ptr [r8 + 8768]
	vmovdqu32 zmm30, zmmword ptr [r8 + 8832]
	vshufps zmm10, zmm12, zmm13, 0x44
	vshufps zmm12, zmm12, zmm13, 0xee
	vshufps zmm26, zmm14, zmm15, 0x44
	vshufps zmm14, zmm14, zmm15, 0xee
	vshufps zmm15, zmm10, zmm26, 0xdd
	vshufps zmm13, zmm12, zmm14, 0x88
	vshufps zmm12, zmm12, zmm14, 0xdd
	vshufps zmm10, zmm10, zmm26, 0x88
	vshufps zmm14, zmm16, zmm17, 0x44
	vshufps zmm16, zmm16, zmm17, 0xee
	vshufps zmm26, zmm18, zmm19, 0x44
	vshufps zmm18, zmm18, zmm19, 0xee
	vshufps zmm19, zmm14, zmm26, 0xdd
	vshufps zmm17, zmm16, zmm18, 0x88
	vshufps zmm16, zmm16, zmm18, 0xdd
	vshufps zmm14, zmm14, zmm26, 0x88
	vshufps zmm18, zmm20, zmm21, 0x44
	vshufps zmm20, zmm20, zmm21, 0xee
	vshufps zmm26, zmm22, zmm23, 0x44
	vshufps zmm22, zmm22, zmm23, 0xee
	vshufps zmm23, zmm18, zmm26, 0xdd
	vshufps zmm21, zmm20, zmm22, 0x88
	vshufps zmm20, zmm20, zmm22, 0xdd
	vshufps zmm18, zmm18, zmm26, 0x88
	vmovdqa32 zmm26, zmm29
	vpermi2q zmm26, zmm17, zmm21
	vmovdqa32 zmm22, zmm30
	vpermi2q zmm22, zmm17, zmm21
	vmovdqa32 zmm17, zmm29
	vpermi2q zmm17, zmm19, zmm23
	vmovdqa32 zmm21, zmm30
	vpermi2q zmm21, zmm19, zmm23
	vmovdqa32 zmm19, zmm29
	vpermi2q zmm19, zmm16, zmm20
	vmovdqa32 zmm23, zmm30
	vpermi2q zmm23, zmm16, zmm20
	vmovdqa32 zmm16, zmm29
	vpermi2q zmm16, zmm14, zmm18
	vmovdqa32 zmm20, zmm30
	vpermi2q zmm20, zmm14, zmm18
	vmovdqa32 zmm18, zmm26
	vmovdqa32 zmm26, zmm29
	vpermi2q zmm26, zmm9, zmm13
	vmovdqa32 zmm14, zmm30
	vpermi2q zmm14, zmm9, zmm13
	vmovdqa32 zmm9, zmm29
	vpermi2q zmm9, zmm11, zmm15
	vmovdqa32 zmm13, zmm30
	vpermi2q zmm13, zmm11, zmm15
	vmovdqa32 zmm11, zmm29
	vpermi2q zmm11, zmm8, zmm12
	vmovdqa32 zmm15, zmm30
	vpermi2q zmm15, zmm8, zmm12
	vmovdqa32 zmm8, zmm29
	vpermi2q zmm8, zmm25, zmm10
	vmovdqa32 zmm12, zmm30
	vpermi2q zmm12, zmm25, zmm10
	vmovdqa32 zmm10, zmm26
	vmovdqu32 zmm27, zmmword ptr [r8 + 8704]
	vpshufb zmm8, zmm8, zmm27
	vpshufb zmm9, zmm9, zmm27
	vpshufb zmm10, zmm10, zmm27
	vpshufb zmm11, zmm11, zmm27
	vpshufb zmm12, zmm12, zmm27
	vpshufb zmm13, zmm13, zmm27
	vpshufb zmm14, zmm14, zmm27
	vpshufb zmm15, zmm15, zmm27
	vpshufb zmm16, zmm16, zmm27
	vpshufb zmm17, zmm17, zmm27
	vpshufb zmm18, zmm18, zmm27
	vpshufb zmm19, zmm19, zmm27
	vpshufb zmm20, zmm20, zmm27
	vpshufb zmm21, zmm21, zmm27
	vpshufb zmm22, zmm22, zmm27
	vpshufb zmm23, zmm23, zmm27
	vmovdqu32 zmm0, zmmword ptr [r8 + 8192]
	vmovdqu32 zmm1, zmmword ptr [r8 + 8256]
	vmovdqu32 zmm2, zmmword ptr [r8 + 8320]
	vmovdqu32 zmm3, zmmword ptr [r8 + 8384]
	vmovdqu32 zmm4, zmmword ptr [r8 + 8448]
	vmovdqu32 zmm5, zmmword ptr [r8 + 8512]
	vmovdqu32 zmm6, zmmword ptr [r8 + 8576]
	vmovdqu32 zmm7, zmmword ptr [r8 + 8640]
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 0]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 64]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 128]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 192]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 256]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 320]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 384]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 448]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 512]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 576]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 640]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 704]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 768]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 832]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 896]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 960]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 1024]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 1088]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 1152]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 1216]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 1280]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 1344]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 1408]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 1472]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 1536]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 1600]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 1664]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 1728]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 1792]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 1856]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 1920]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 1984]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 2048]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 2112]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 2176]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 2240]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 2304]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 2368]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 2432]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 2496]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 2560]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 2624]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 2688]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 2752]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 2816]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 2880]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 2944]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 3008]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 3072]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 3136]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 3200]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 3264]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 3328]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 3392]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 3456]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 3520]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 3584]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 3648]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 3712]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 3776]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 3840]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 3904]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 3968]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 4032]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm0, zmm0, zmmword ptr [r8 + 8192]
	vmovdqa32 zmm8, zmm0
	vpaddd zmm1, zmm1, zmmword ptr [r8 + 8256]
	vmovdqa32 zmm9, zmm1
	vpaddd zmm2, zmm2, zmmword ptr [r8 + 8320]
	vmovdqa32 zmm10, zmm2
	vpaddd zmm3, zmm3, zmmword ptr [r8 + 8384]
	vmovdqa32 zmm11, zmm3
	vpaddd zmm4, zmm4, zmmword ptr [r8 + 8448]
	vmovdqa32 zmm12, zmm4
	vpaddd zmm5, zmm5, zmmword ptr [r8 + 8512]
	vmovdqa32 zmm13, zmm5
	vpaddd zmm6, zmm6, zmmword ptr [r8 + 8576]
	vmovdqa32 zmm14, zmm6
	vpaddd zmm7, zmm7, zmmword ptr [r8 + 8640]
	vmovdqa32 zmm15, zmm7
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 4096]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 4160]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 4224]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 4288]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 4352]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 4416]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 4480]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 4544]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 4608]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 4672]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 4736]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 4800]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 4864]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 4928]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 4992]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 5056]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 5120]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 5184]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 5248]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 5312]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 5376]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 5440]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 5504]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 5568]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 5632]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 5696]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 5760]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 5824]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 5888]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 5952]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 6016]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 6080]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 6144]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 6208]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 6272]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 6336]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 6400]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 6464]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 6528]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 6592]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 6656]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 6720]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 6784]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 6848]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 6912]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 6976]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 7040]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 7104]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 7168]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 7232]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 7296]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 7360]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 7424]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 7488]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 7552]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 7616]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 7680]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 7744]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 7808]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 7872]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 7936]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 8000]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 8064]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 8128]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm0, zmm0, zmm8
	vpaddd zmm1, zmm1, zmm9
	vpaddd zmm2, zmm2, zmm10
	vpaddd zmm3, zmm3, zmm11
	vpaddd zmm4, zmm4, zmm12
	vpaddd zmm5, zmm5, zmm13
	vpaddd zmm6, zmm6, zmm14
	vpaddd zmm7, zmm7, zmm15
	vmovdqu32 zmm30, zmmword ptr [r8 + 8896]
	vmovdqu32 zmm31, zmmword ptr [r8 + 8960]
	vmovdqa32 zmm25, zmm30
	vmovdqa32 zmm26, zmm30
	vpermi2d zmm25, zmm0, zmm4
	vpermi2d zmm26, zmm1, zmm5
	vmovdqa32 zmm27, zmm31
	vmovdqa32 zmm28, zmm31
	vpermi2d zmm27, zmm0, zmm4
	vpermi2d zmm28, zmm1, zmm5
	vmovdqa32 zmm0, zmm30
	vmovdqa32 zmm1, zmm30
	vpermi2d zmm0, zmm2, zmm6
	vpermi2d zmm1, zmm3, zmm7
	vmovdqa32 zmm4, zmm31
	vmovdqa32 zmm5, zmm31
	vpermi2d zmm4, zmm2, zmm6
	vpermi2d zmm5, zmm3, zmm7
	vshufps zmm6, zmm25, zmm26, 0x88
	vshufps zmm7, zmm25, zmm26, 0xdd
	vshufps zmm26, zmm27, zmm28, 0x88
	vshufps zmm25, zmm27, zmm28, 0xdd
	vshufps zmm27, zmm4, zmm5, 0x88
	vshufps zmm28, zmm4, zmm5, 0xdd
	vshufps zmm4, zmm0, zmm1, 0x88
	vshufps zmm5, zmm0, zmm1, 0xdd
	vmovdqa32 zmm0, zmm30
	vmovdqa32 zmm1, zmm30
	vpermi2d zmm0, zmm6, zmm4
	vpermi2d zmm1, zmm7, zmm5
	vmovdqa32 zmm2, zmm31
	vmovdqa32 zmm3, zmm31
	vpermi2d zmm2, zmm6, zmm4
	vpermi2d zmm3, zmm7, zmm5
	vmovdqa32 zmm4, zmm30
	vmovdqa32 zmm5, zmm30
	vpermi2d zmm4, zmm26, zmm27
	vpermi2d zmm5, zmm25, zmm28
	vmovdqa32 zmm6, zmm31
	vmovdqa32 zmm7, zmm31
	vpermi2d zmm6, zmm26, zmm27
	vpermi2d zmm7, zmm25, zmm28
	vmovdqu32 zmm27, zmmword ptr [r8 + 8704]
	vpshufb zmm0, zmm0, zmm27
	vmovdqu32 zmmword ptr [rdi + 0], zmm0
	vpshufb zmm1, zmm1, zmm27
	vmovdqu32 zmmword ptr [rdi + 64], zmm1
	vpshufb zmm2, zmm2, zmm27
	vmovdqu32 zmmword ptr [rdi + 128], zmm2
	vpshufb zmm3, zmm3, zmm27
	vmovdqu32 zmmword ptr [rdi + 192], zmm3
	vpshufb zmm4, zmm4, zmm27
	vmovdqu32 zmmword ptr [rdi + 256], zmm4
	vpshufb zmm5, zmm5, zmm27
	vmovdqu32 zmmword ptr [rdi + 320], zmm5
	vpshufb zmm6, zmm6, zmm27
	vmovdqu32 zmmword ptr [rdi + 384], zmm6
	vpshufb zmm7, zmm7, zmm27
	vmovdqu32 zmmword ptr [rdi + 448], zmm7
	add rsi, 512
	add rdx, 512
	add rdi, 512
	sub rcx, 1
	jnz .Lssz_sha256_avx512_columns_2
.Lssz_sha256_avx512_columns_3111:
	vzeroupper
	ret
	.globl SYMBOL(ssz_sha256_avx512_fixed)
	.p2align 6
SYMBOL(ssz_sha256_avx512_fixed):
	test rcx, rcx
	jz .Lssz_sha256_avx512_fixed_3111
.Lssz_sha256_avx512_fixed_2:
	vmovdqu ymm8, ymmword ptr [rsi + 0]
	vmovdqu32 ymm16, ymmword ptr [rdx + 0]
	vmovdqu ymm9, ymmword ptr [rsi + 32]
	vmovdqu32 ymm17, ymmword ptr [rdx + 0]
	vmovdqu ymm10, ymmword ptr [rsi + 64]
	vmovdqu32 ymm18, ymmword ptr [rdx + 0]
	vmovdqu ymm11, ymmword ptr [rsi + 96]
	vmovdqu32 ymm19, ymmword ptr [rdx + 0]
	vmovdqu ymm12, ymmword ptr [rsi + 128]
	vmovdqu32 ymm20, ymmword ptr [rdx + 0]
	vmovdqu ymm13, ymmword ptr [rsi + 160]
	vmovdqu32 ymm21, ymmword ptr [rdx + 0]
	vmovdqu ymm14, ymmword ptr [rsi + 192]
	vmovdqu32 ymm22, ymmword ptr [rdx + 0]
	vmovdqu ymm15, ymmword ptr [rsi + 224]
	vmovdqu32 ymm23, ymmword ptr [rdx + 0]
	vinserti64x4 zmm8, zmm8, ymmword ptr [rsi + 256], 1
	vinserti64x4 zmm16, zmm16, ymmword ptr [rdx + 0], 1
	vinserti64x4 zmm9, zmm9, ymmword ptr [rsi + 288], 1
	vinserti64x4 zmm17, zmm17, ymmword ptr [rdx + 0], 1
	vinserti64x4 zmm10, zmm10, ymmword ptr [rsi + 320], 1
	vinserti64x4 zmm18, zmm18, ymmword ptr [rdx + 0], 1
	vinserti64x4 zmm11, zmm11, ymmword ptr [rsi + 352], 1
	vinserti64x4 zmm19, zmm19, ymmword ptr [rdx + 0], 1
	vinserti64x4 zmm12, zmm12, ymmword ptr [rsi + 384], 1
	vinserti64x4 zmm20, zmm20, ymmword ptr [rdx + 0], 1
	vinserti64x4 zmm13, zmm13, ymmword ptr [rsi + 416], 1
	vinserti64x4 zmm21, zmm21, ymmword ptr [rdx + 0], 1
	vinserti64x4 zmm14, zmm14, ymmword ptr [rsi + 448], 1
	vinserti64x4 zmm22, zmm22, ymmword ptr [rdx + 0], 1
	vinserti64x4 zmm15, zmm15, ymmword ptr [rsi + 480], 1
	vinserti64x4 zmm23, zmm23, ymmword ptr [rdx + 0], 1
	vshufps zmm25, zmm8, zmm9, 0x44
	vshufps zmm8, zmm8, zmm9, 0xee
	vshufps zmm26, zmm10, zmm11, 0x44
	vshufps zmm10, zmm10, zmm11, 0xee
	vshufps zmm11, zmm25, zmm26, 0xdd
	vshufps zmm9, zmm8, zmm10, 0x88
	vshufps zmm8, zmm8, zmm10, 0xdd
	vshufps zmm25, zmm25, zmm26, 0x88
	vmovdqu32 zmm29, zmmword ptr [r8 + 8768]
	vmovdqu32 zmm30, zmmword ptr [r8 + 8832]
	vshufps zmm10, zmm12, zmm13, 0x44
	vshufps zmm12, zmm12, zmm13, 0xee
	vshufps zmm26, zmm14, zmm15, 0x44
	vshufps zmm14, zmm14, zmm15, 0xee
	vshufps zmm15, zmm10, zmm26, 0xdd
	vshufps zmm13, zmm12, zmm14, 0x88
	vshufps zmm12, zmm12, zmm14, 0xdd
	vshufps zmm10, zmm10, zmm26, 0x88
	vshufps zmm14, zmm16, zmm17, 0x44
	vshufps zmm16, zmm16, zmm17, 0xee
	vshufps zmm26, zmm18, zmm19, 0x44
	vshufps zmm18, zmm18, zmm19, 0xee
	vshufps zmm19, zmm14, zmm26, 0xdd
	vshufps zmm17, zmm16, zmm18, 0x88
	vshufps zmm16, zmm16, zmm18, 0xdd
	vshufps zmm14, zmm14, zmm26, 0x88
	vshufps zmm18, zmm20, zmm21, 0x44
	vshufps zmm20, zmm20, zmm21, 0xee
	vshufps zmm26, zmm22, zmm23, 0x44
	vshufps zmm22, zmm22, zmm23, 0xee
	vshufps zmm23, zmm18, zmm26, 0xdd
	vshufps zmm21, zmm20, zmm22, 0x88
	vshufps zmm20, zmm20, zmm22, 0xdd
	vshufps zmm18, zmm18, zmm26, 0x88
	vmovdqa32 zmm26, zmm29
	vpermi2q zmm26, zmm17, zmm21
	vmovdqa32 zmm22, zmm30
	vpermi2q zmm22, zmm17, zmm21
	vmovdqa32 zmm17, zmm29
	vpermi2q zmm17, zmm19, zmm23
	vmovdqa32 zmm21, zmm30
	vpermi2q zmm21, zmm19, zmm23
	vmovdqa32 zmm19, zmm29
	vpermi2q zmm19, zmm16, zmm20
	vmovdqa32 zmm23, zmm30
	vpermi2q zmm23, zmm16, zmm20
	vmovdqa32 zmm16, zmm29
	vpermi2q zmm16, zmm14, zmm18
	vmovdqa32 zmm20, zmm30
	vpermi2q zmm20, zmm14, zmm18
	vmovdqa32 zmm18, zmm26
	vmovdqa32 zmm26, zmm29
	vpermi2q zmm26, zmm9, zmm13
	vmovdqa32 zmm14, zmm30
	vpermi2q zmm14, zmm9, zmm13
	vmovdqa32 zmm9, zmm29
	vpermi2q zmm9, zmm11, zmm15
	vmovdqa32 zmm13, zmm30
	vpermi2q zmm13, zmm11, zmm15
	vmovdqa32 zmm11, zmm29
	vpermi2q zmm11, zmm8, zmm12
	vmovdqa32 zmm15, zmm30
	vpermi2q zmm15, zmm8, zmm12
	vmovdqa32 zmm8, zmm29
	vpermi2q zmm8, zmm25, zmm10
	vmovdqa32 zmm12, zmm30
	vpermi2q zmm12, zmm25, zmm10
	vmovdqa32 zmm10, zmm26
	vmovdqu32 zmm27, zmmword ptr [r8 + 8704]
	vpshufb zmm8, zmm8, zmm27
	vpshufb zmm9, zmm9, zmm27
	vpshufb zmm10, zmm10, zmm27
	vpshufb zmm11, zmm11, zmm27
	vpshufb zmm12, zmm12, zmm27
	vpshufb zmm13, zmm13, zmm27
	vpshufb zmm14, zmm14, zmm27
	vpshufb zmm15, zmm15, zmm27
	vpshufb zmm16, zmm16, zmm27
	vpshufb zmm17, zmm17, zmm27
	vpshufb zmm18, zmm18, zmm27
	vpshufb zmm19, zmm19, zmm27
	vpshufb zmm20, zmm20, zmm27
	vpshufb zmm21, zmm21, zmm27
	vpshufb zmm22, zmm22, zmm27
	vpshufb zmm23, zmm23, zmm27
	vmovdqu32 zmm0, zmmword ptr [r8 + 8192]
	vmovdqu32 zmm1, zmmword ptr [r8 + 8256]
	vmovdqu32 zmm2, zmmword ptr [r8 + 8320]
	vmovdqu32 zmm3, zmmword ptr [r8 + 8384]
	vmovdqu32 zmm4, zmmword ptr [r8 + 8448]
	vmovdqu32 zmm5, zmmword ptr [r8 + 8512]
	vmovdqu32 zmm6, zmmword ptr [r8 + 8576]
	vmovdqu32 zmm7, zmmword ptr [r8 + 8640]
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 0]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 64]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 128]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 192]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 256]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 320]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 384]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 448]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 512]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 576]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 640]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 704]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 768]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 832]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 896]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 960]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 1024]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 1088]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 1152]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 1216]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 1280]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 1344]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 1408]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 1472]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 1536]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 1600]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 1664]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 1728]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 1792]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 1856]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 1920]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 1984]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 2048]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm22, 17
	vprord zmm30, zmm22, 19
	vpsrld zmm31, zmm22, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm8, zmm8, zmm17
	vprord zmm29, zmm9, 7
	vprord zmm30, zmm9, 18
	vpsrld zmm31, zmm9, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm8, zmm8, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 2112]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm23, 17
	vprord zmm30, zmm23, 19
	vpsrld zmm31, zmm23, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm9, zmm9, zmm18
	vprord zmm29, zmm10, 7
	vprord zmm30, zmm10, 18
	vpsrld zmm31, zmm10, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm9, zmm9, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 2176]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm8, 17
	vprord zmm30, zmm8, 19
	vpsrld zmm31, zmm8, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm10, zmm10, zmm19
	vprord zmm29, zmm11, 7
	vprord zmm30, zmm11, 18
	vpsrld zmm31, zmm11, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm10, zmm10, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 2240]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm9, 17
	vprord zmm30, zmm9, 19
	vpsrld zmm31, zmm9, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm11, zmm11, zmm20
	vprord zmm29, zmm12, 7
	vprord zmm30, zmm12, 18
	vpsrld zmm31, zmm12, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm11, zmm11, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 2304]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm10, 17
	vprord zmm30, zmm10, 19
	vpsrld zmm31, zmm10, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm12, zmm12, zmm21
	vprord zmm29, zmm13, 7
	vprord zmm30, zmm13, 18
	vpsrld zmm31, zmm13, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm12, zmm12, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 2368]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm11, 17
	vprord zmm30, zmm11, 19
	vpsrld zmm31, zmm11, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm13, zmm13, zmm22
	vprord zmm29, zmm14, 7
	vprord zmm30, zmm14, 18
	vpsrld zmm31, zmm14, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm13, zmm13, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 2432]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm12, 17
	vprord zmm30, zmm12, 19
	vpsrld zmm31, zmm12, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm14, zmm14, zmm23
	vprord zmm29, zmm15, 7
	vprord zmm30, zmm15, 18
	vpsrld zmm31, zmm15, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm14, zmm14, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 2496]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm13, 17
	vprord zmm30, zmm13, 19
	vpsrld zmm31, zmm13, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm15, zmm15, zmm8
	vprord zmm29, zmm16, 7
	vprord zmm30, zmm16, 18
	vpsrld zmm31, zmm16, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm15, zmm15, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 2560]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vprord zmm29, zmm14, 17
	vprord zmm30, zmm14, 19
	vpsrld zmm31, zmm14, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm16, zmm16, zmm9
	vprord zmm29, zmm17, 7
	vprord zmm30, zmm17, 18
	vpsrld zmm31, zmm17, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm16, zmm16, zmm29
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 2624]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vprord zmm29, zmm15, 17
	vprord zmm30, zmm15, 19
	vpsrld zmm31, zmm15, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm17, zmm17, zmm10
	vprord zmm29, zmm18, 7
	vprord zmm30, zmm18, 18
	vpsrld zmm31, zmm18, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm17, zmm17, zmm29
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 2688]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vprord zmm29, zmm16, 17
	vprord zmm30, zmm16, 19
	vpsrld zmm31, zmm16, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm18, zmm18, zmm11
	vprord zmm29, zmm19, 7
	vprord zmm30, zmm19, 18
	vpsrld zmm31, zmm19, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm18, zmm18, zmm29
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 2752]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vprord zmm29, zmm17, 17
	vprord zmm30, zmm17, 19
	vpsrld zmm31, zmm17, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm19, zmm19, zmm12
	vprord zmm29, zmm20, 7
	vprord zmm30, zmm20, 18
	vpsrld zmm31, zmm20, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm19, zmm19, zmm29
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 2816]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vprord zmm29, zmm18, 17
	vprord zmm30, zmm18, 19
	vpsrld zmm31, zmm18, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm20, zmm20, zmm13
	vprord zmm29, zmm21, 7
	vprord zmm30, zmm21, 18
	vpsrld zmm31, zmm21, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm20, zmm20, zmm29
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 2880]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vprord zmm29, zmm19, 17
	vprord zmm30, zmm19, 19
	vpsrld zmm31, zmm19, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm21, zmm21, zmm14
	vprord zmm29, zmm22, 7
	vprord zmm30, zmm22, 18
	vpsrld zmm31, zmm22, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm21, zmm21, zmm29
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 2944]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vprord zmm29, zmm20, 17
	vprord zmm30, zmm20, 19
	vpsrld zmm31, zmm20, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm22, zmm22, zmm15
	vprord zmm29, zmm23, 7
	vprord zmm30, zmm23, 18
	vpsrld zmm31, zmm23, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm22, zmm22, zmm29
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 3008]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vprord zmm29, zmm21, 17
	vprord zmm30, zmm21, 19
	vpsrld zmm31, zmm21, 10
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm23, zmm23, zmm16
	vprord zmm29, zmm8, 7
	vprord zmm30, zmm8, 18
	vpsrld zmm31, zmm8, 3
	vpternlogd zmm29, zmm30, zmm31, 0x96
	vpaddd zmm23, zmm23, zmm29
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 3072]
	vpaddd zmm24, zmm24, zmm8
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 3136]
	vpaddd zmm24, zmm24, zmm9
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 3200]
	vpaddd zmm24, zmm24, zmm10
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 3264]
	vpaddd zmm24, zmm24, zmm11
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 3328]
	vpaddd zmm24, zmm24, zmm12
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 3392]
	vpaddd zmm24, zmm24, zmm13
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 3456]
	vpaddd zmm24, zmm24, zmm14
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 3520]
	vpaddd zmm24, zmm24, zmm15
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 3584]
	vpaddd zmm24, zmm24, zmm16
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 3648]
	vpaddd zmm24, zmm24, zmm17
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 3712]
	vpaddd zmm24, zmm24, zmm18
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 3776]
	vpaddd zmm24, zmm24, zmm19
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 3840]
	vpaddd zmm24, zmm24, zmm20
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 3904]
	vpaddd zmm24, zmm24, zmm21
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 3968]
	vpaddd zmm24, zmm24, zmm22
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 4032]
	vpaddd zmm24, zmm24, zmm23
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm0, zmm0, zmmword ptr [r8 + 8192]
	vmovdqa32 zmm8, zmm0
	vpaddd zmm1, zmm1, zmmword ptr [r8 + 8256]
	vmovdqa32 zmm9, zmm1
	vpaddd zmm2, zmm2, zmmword ptr [r8 + 8320]
	vmovdqa32 zmm10, zmm2
	vpaddd zmm3, zmm3, zmmword ptr [r8 + 8384]
	vmovdqa32 zmm11, zmm3
	vpaddd zmm4, zmm4, zmmword ptr [r8 + 8448]
	vmovdqa32 zmm12, zmm4
	vpaddd zmm5, zmm5, zmmword ptr [r8 + 8512]
	vmovdqa32 zmm13, zmm5
	vpaddd zmm6, zmm6, zmmword ptr [r8 + 8576]
	vmovdqa32 zmm14, zmm6
	vpaddd zmm7, zmm7, zmmword ptr [r8 + 8640]
	vmovdqa32 zmm15, zmm7
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 4096]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 4160]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 4224]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 4288]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 4352]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 4416]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 4480]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 4544]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 4608]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 4672]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 4736]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 4800]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 4864]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 4928]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 4992]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 5056]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 5120]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 5184]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 5248]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 5312]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 5376]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 5440]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 5504]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 5568]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 5632]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 5696]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 5760]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 5824]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 5888]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 5952]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 6016]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 6080]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 6144]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 6208]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 6272]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 6336]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 6400]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 6464]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 6528]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 6592]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 6656]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 6720]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 6784]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 6848]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 6912]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 6976]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 7040]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 7104]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 7168]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 7232]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 7296]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 7360]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 7424]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 7488]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 7552]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 7616]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm24, zmm7, zmmword ptr [r8 + 7680]
	vmovdqa32 zmm25, zmm4
	vprord zmm26, zmm4, 6
	vprord zmm27, zmm4, 11
	vprord zmm28, zmm4, 25
	vpternlogd zmm25, zmm5, zmm6, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm3, zmm3, zmm24
	vprord zmm7, zmm0, 2
	vprord zmm27, zmm0, 13
	vprord zmm28, zmm0, 22
	vmovdqa32 zmm25, zmm0
	vpternlogd zmm25, zmm1, zmm2, 0xe8
	vpternlogd zmm7, zmm27, zmm28, 0x96
	vpaddd zmm7, zmm7, zmm25
	vpaddd zmm7, zmm7, zmm24
	vpaddd zmm24, zmm6, zmmword ptr [r8 + 7744]
	vmovdqa32 zmm25, zmm3
	vprord zmm26, zmm3, 6
	vprord zmm27, zmm3, 11
	vprord zmm28, zmm3, 25
	vpternlogd zmm25, zmm4, zmm5, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm2, zmm2, zmm24
	vprord zmm6, zmm7, 2
	vprord zmm27, zmm7, 13
	vprord zmm28, zmm7, 22
	vmovdqa32 zmm25, zmm7
	vpternlogd zmm25, zmm0, zmm1, 0xe8
	vpternlogd zmm6, zmm27, zmm28, 0x96
	vpaddd zmm6, zmm6, zmm25
	vpaddd zmm6, zmm6, zmm24
	vpaddd zmm24, zmm5, zmmword ptr [r8 + 7808]
	vmovdqa32 zmm25, zmm2
	vprord zmm26, zmm2, 6
	vprord zmm27, zmm2, 11
	vprord zmm28, zmm2, 25
	vpternlogd zmm25, zmm3, zmm4, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm1, zmm1, zmm24
	vprord zmm5, zmm6, 2
	vprord zmm27, zmm6, 13
	vprord zmm28, zmm6, 22
	vmovdqa32 zmm25, zmm6
	vpternlogd zmm25, zmm7, zmm0, 0xe8
	vpternlogd zmm5, zmm27, zmm28, 0x96
	vpaddd zmm5, zmm5, zmm25
	vpaddd zmm5, zmm5, zmm24
	vpaddd zmm24, zmm4, zmmword ptr [r8 + 7872]
	vmovdqa32 zmm25, zmm1
	vprord zmm26, zmm1, 6
	vprord zmm27, zmm1, 11
	vprord zmm28, zmm1, 25
	vpternlogd zmm25, zmm2, zmm3, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm0, zmm0, zmm24
	vprord zmm4, zmm5, 2
	vprord zmm27, zmm5, 13
	vprord zmm28, zmm5, 22
	vmovdqa32 zmm25, zmm5
	vpternlogd zmm25, zmm6, zmm7, 0xe8
	vpternlogd zmm4, zmm27, zmm28, 0x96
	vpaddd zmm4, zmm4, zmm25
	vpaddd zmm4, zmm4, zmm24
	vpaddd zmm24, zmm3, zmmword ptr [r8 + 7936]
	vmovdqa32 zmm25, zmm0
	vprord zmm26, zmm0, 6
	vprord zmm27, zmm0, 11
	vprord zmm28, zmm0, 25
	vpternlogd zmm25, zmm1, zmm2, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm7, zmm7, zmm24
	vprord zmm3, zmm4, 2
	vprord zmm27, zmm4, 13
	vprord zmm28, zmm4, 22
	vmovdqa32 zmm25, zmm4
	vpternlogd zmm25, zmm5, zmm6, 0xe8
	vpternlogd zmm3, zmm27, zmm28, 0x96
	vpaddd zmm3, zmm3, zmm25
	vpaddd zmm3, zmm3, zmm24
	vpaddd zmm24, zmm2, zmmword ptr [r8 + 8000]
	vmovdqa32 zmm25, zmm7
	vprord zmm26, zmm7, 6
	vprord zmm27, zmm7, 11
	vprord zmm28, zmm7, 25
	vpternlogd zmm25, zmm0, zmm1, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm6, zmm6, zmm24
	vprord zmm2, zmm3, 2
	vprord zmm27, zmm3, 13
	vprord zmm28, zmm3, 22
	vmovdqa32 zmm25, zmm3
	vpternlogd zmm25, zmm4, zmm5, 0xe8
	vpternlogd zmm2, zmm27, zmm28, 0x96
	vpaddd zmm2, zmm2, zmm25
	vpaddd zmm2, zmm2, zmm24
	vpaddd zmm24, zmm1, zmmword ptr [r8 + 8064]
	vmovdqa32 zmm25, zmm6
	vprord zmm26, zmm6, 6
	vprord zmm27, zmm6, 11
	vprord zmm28, zmm6, 25
	vpternlogd zmm25, zmm7, zmm0, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm5, zmm5, zmm24
	vprord zmm1, zmm2, 2
	vprord zmm27, zmm2, 13
	vprord zmm28, zmm2, 22
	vmovdqa32 zmm25, zmm2
	vpternlogd zmm25, zmm3, zmm4, 0xe8
	vpternlogd zmm1, zmm27, zmm28, 0x96
	vpaddd zmm1, zmm1, zmm25
	vpaddd zmm1, zmm1, zmm24
	vpaddd zmm24, zmm0, zmmword ptr [r8 + 8128]
	vmovdqa32 zmm25, zmm5
	vprord zmm26, zmm5, 6
	vprord zmm27, zmm5, 11
	vprord zmm28, zmm5, 25
	vpternlogd zmm25, zmm6, zmm7, 0xca
	vpternlogd zmm26, zmm27, zmm28, 0x96
	vpaddd zmm24, zmm24, zmm25
	vpaddd zmm24, zmm24, zmm26
	vpaddd zmm4, zmm4, zmm24
	vprord zmm0, zmm1, 2
	vprord zmm27, zmm1, 13
	vprord zmm28, zmm1, 22
	vmovdqa32 zmm25, zmm1
	vpternlogd zmm25, zmm2, zmm3, 0xe8
	vpternlogd zmm0, zmm27, zmm28, 0x96
	vpaddd zmm0, zmm0, zmm25
	vpaddd zmm0, zmm0, zmm24
	vpaddd zmm0, zmm0, zmm8
	vpaddd zmm1, zmm1, zmm9
	vpaddd zmm2, zmm2, zmm10
	vpaddd zmm3, zmm3, zmm11
	vpaddd zmm4, zmm4, zmm12
	vpaddd zmm5, zmm5, zmm13
	vpaddd zmm6, zmm6, zmm14
	vpaddd zmm7, zmm7, zmm15
	vmovdqu32 zmm30, zmmword ptr [r8 + 8896]
	vmovdqu32 zmm31, zmmword ptr [r8 + 8960]
	vmovdqa32 zmm25, zmm30
	vmovdqa32 zmm26, zmm30
	vpermi2d zmm25, zmm0, zmm4
	vpermi2d zmm26, zmm1, zmm5
	vmovdqa32 zmm27, zmm31
	vmovdqa32 zmm28, zmm31
	vpermi2d zmm27, zmm0, zmm4
	vpermi2d zmm28, zmm1, zmm5
	vmovdqa32 zmm0, zmm30
	vmovdqa32 zmm1, zmm30
	vpermi2d zmm0, zmm2, zmm6
	vpermi2d zmm1, zmm3, zmm7
	vmovdqa32 zmm4, zmm31
	vmovdqa32 zmm5, zmm31
	vpermi2d zmm4, zmm2, zmm6
	vpermi2d zmm5, zmm3, zmm7
	vshufps zmm6, zmm25, zmm26, 0x88
	vshufps zmm7, zmm25, zmm26, 0xdd
	vshufps zmm26, zmm27, zmm28, 0x88
	vshufps zmm25, zmm27, zmm28, 0xdd
	vshufps zmm27, zmm4, zmm5, 0x88
	vshufps zmm28, zmm4, zmm5, 0xdd
	vshufps zmm4, zmm0, zmm1, 0x88
	vshufps zmm5, zmm0, zmm1, 0xdd
	vmovdqa32 zmm0, zmm30
	vmovdqa32 zmm1, zmm30
	vpermi2d zmm0, zmm6, zmm4
	vpermi2d zmm1, zmm7, zmm5
	vmovdqa32 zmm2, zmm31
	vmovdqa32 zmm3, zmm31
	vpermi2d zmm2, zmm6, zmm4
	vpermi2d zmm3, zmm7, zmm5
	vmovdqa32 zmm4, zmm30
	vmovdqa32 zmm5, zmm30
	vpermi2d zmm4, zmm26, zmm27
	vpermi2d zmm5, zmm25, zmm28
	vmovdqa32 zmm6, zmm31
	vmovdqa32 zmm7, zmm31
	vpermi2d zmm6, zmm26, zmm27
	vpermi2d zmm7, zmm25, zmm28
	vmovdqu32 zmm27, zmmword ptr [r8 + 8704]
	vpshufb zmm0, zmm0, zmm27
	vmovdqu32 zmmword ptr [rdi + 0], zmm0
	vpshufb zmm1, zmm1, zmm27
	vmovdqu32 zmmword ptr [rdi + 64], zmm1
	vpshufb zmm2, zmm2, zmm27
	vmovdqu32 zmmword ptr [rdi + 128], zmm2
	vpshufb zmm3, zmm3, zmm27
	vmovdqu32 zmmword ptr [rdi + 192], zmm3
	vpshufb zmm4, zmm4, zmm27
	vmovdqu32 zmmword ptr [rdi + 256], zmm4
	vpshufb zmm5, zmm5, zmm27
	vmovdqu32 zmmword ptr [rdi + 320], zmm5
	vpshufb zmm6, zmm6, zmm27
	vmovdqu32 zmmword ptr [rdi + 384], zmm6
	vpshufb zmm7, zmm7, zmm27
	vmovdqu32 zmmword ptr [rdi + 448], zmm7
	add rsi, 512
	add rdx, 0
	add rdi, 512
	sub rcx, 1
	jnz .Lssz_sha256_avx512_fixed_2
.Lssz_sha256_avx512_fixed_3111:
	vzeroupper
	ret
	.globl SYMBOL(ssz_sha256_shani_pairs)
	.p2align 6
SYMBOL(ssz_sha256_shani_pairs):
	test rcx, rcx
	jz .Lssz_sha256_shani_pairs_237
	movdqu xmm10, xmmword ptr [r8 + 9568]
.Lssz_sha256_shani_pairs_3:
	movdqu xmm3, xmmword ptr [rsi + 0]
	pshufb xmm3, xmm10
	movdqu xmm4, xmmword ptr [rsi + 16]
	pshufb xmm4, xmm10
	movdqu xmm5, xmmword ptr [rdx + 0]
	pshufb xmm5, xmm10
	movdqu xmm6, xmmword ptr [rdx + 16]
	pshufb xmm6, xmm10
	movdqu xmm1, xmmword ptr [r8 + 9536]
	movdqu xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	paddd xmm1, xmmword ptr [r8 + 9536]
	paddd xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm8, xmm1
	movdqa xmm9, xmm2
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	paddd xmm1, xmm8
	paddd xmm2, xmm9
	pshufd xmm1, xmm1, 0x1b
	pshufd xmm2, xmm2, 0xb1
	movdqa xmm7, xmm1
	pblendw xmm7, xmm2, 0xf0
	palignr xmm2, xmm1, 8
	pshufb xmm7, xmm10
	pshufb xmm2, xmm10
	movdqu xmmword ptr [rdi + 0], xmm7
	movdqu xmmword ptr [rdi + 16], xmm2
	add rsi, 64
	add rdx, 64
	add rdi, 32
	sub rcx, 1
	jnz .Lssz_sha256_shani_pairs_3
.Lssz_sha256_shani_pairs_237:
	ret
	.globl SYMBOL(ssz_sha256_shani_columns)
	.p2align 6
SYMBOL(ssz_sha256_shani_columns):
	test rcx, rcx
	jz .Lssz_sha256_shani_columns_237
	movdqu xmm10, xmmword ptr [r8 + 9568]
.Lssz_sha256_shani_columns_3:
	movdqu xmm3, xmmword ptr [rsi + 0]
	pshufb xmm3, xmm10
	movdqu xmm4, xmmword ptr [rsi + 16]
	pshufb xmm4, xmm10
	movdqu xmm5, xmmword ptr [rdx + 0]
	pshufb xmm5, xmm10
	movdqu xmm6, xmmword ptr [rdx + 16]
	pshufb xmm6, xmm10
	movdqu xmm1, xmmword ptr [r8 + 9536]
	movdqu xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	paddd xmm1, xmmword ptr [r8 + 9536]
	paddd xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm8, xmm1
	movdqa xmm9, xmm2
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	paddd xmm1, xmm8
	paddd xmm2, xmm9
	pshufd xmm1, xmm1, 0x1b
	pshufd xmm2, xmm2, 0xb1
	movdqa xmm7, xmm1
	pblendw xmm7, xmm2, 0xf0
	palignr xmm2, xmm1, 8
	pshufb xmm7, xmm10
	pshufb xmm2, xmm10
	movdqu xmmword ptr [rdi + 0], xmm7
	movdqu xmmword ptr [rdi + 16], xmm2
	add rsi, 32
	add rdx, 32
	add rdi, 32
	sub rcx, 1
	jnz .Lssz_sha256_shani_columns_3
.Lssz_sha256_shani_columns_237:
	ret
	.globl SYMBOL(ssz_sha256_shani_fixed)
	.p2align 6
SYMBOL(ssz_sha256_shani_fixed):
	test rcx, rcx
	jz .Lssz_sha256_shani_fixed_237
	movdqu xmm10, xmmword ptr [r8 + 9568]
.Lssz_sha256_shani_fixed_3:
	movdqu xmm3, xmmword ptr [rsi + 0]
	pshufb xmm3, xmm10
	movdqu xmm4, xmmword ptr [rsi + 16]
	pshufb xmm4, xmm10
	movdqu xmm5, xmmword ptr [rdx + 0]
	pshufb xmm5, xmm10
	movdqu xmm6, xmmword ptr [rdx + 16]
	pshufb xmm6, xmm10
	movdqu xmm1, xmmword ptr [r8 + 9536]
	movdqu xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	paddd xmm1, xmmword ptr [r8 + 9536]
	paddd xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm8, xmm1
	movdqa xmm9, xmm2
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	paddd xmm1, xmm8
	paddd xmm2, xmm9
	pshufd xmm1, xmm1, 0x1b
	pshufd xmm2, xmm2, 0xb1
	movdqa xmm7, xmm1
	pblendw xmm7, xmm2, 0xf0
	palignr xmm2, xmm1, 8
	pshufb xmm7, xmm10
	pshufb xmm2, xmm10
	movdqu xmmword ptr [rdi + 0], xmm7
	movdqu xmmword ptr [rdi + 16], xmm2
	add rsi, 32
	add rdx, 0
	add rdi, 32
	sub rcx, 1
	jnz .Lssz_sha256_shani_fixed_3
.Lssz_sha256_shani_fixed_237:
	ret
	.globl SYMBOL(ssz_sha256_shani_dual_pairs)
	.p2align 6
SYMBOL(ssz_sha256_shani_dual_pairs):
	test rcx, rcx
	jz .Lssz_sha256_shani_dual_pairs_466
	movdqu xmm10, xmmword ptr [r8 + 9568]
.Lssz_sha256_shani_dual_pairs_3:
	movdqu xmm3, xmmword ptr [rsi + 0]
	pshufb xmm3, xmm10
	movdqu xmm4, xmmword ptr [rsi + 16]
	pshufb xmm4, xmm10
	movdqu xmm5, xmmword ptr [rdx + 0]
	pshufb xmm5, xmm10
	movdqu xmm6, xmmword ptr [rdx + 16]
	pshufb xmm6, xmm10
	movdqu xmm1, xmmword ptr [r8 + 9536]
	movdqu xmm2, xmmword ptr [r8 + 9552]
	movdqu xmm11, xmmword ptr [rsi + 64]
	pshufb xmm11, xmm10
	movdqu xmm12, xmmword ptr [rsi + 80]
	pshufb xmm12, xmm10
	movdqu xmm13, xmmword ptr [rdx + 64]
	pshufb xmm13, xmm10
	movdqu xmm14, xmmword ptr [rdx + 80]
	pshufb xmm14, xmm10
	movdqu xmm8, xmmword ptr [r8 + 9536]
	movdqu xmm9, xmmword ptr [r8 + 9552]
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	paddd xmm1, xmmword ptr [r8 + 9536]
	paddd xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm3, xmm1
	movdqa xmm4, xmm2
	paddd xmm8, xmmword ptr [r8 + 9536]
	paddd xmm9, xmmword ptr [r8 + 9552]
	movdqa xmm11, xmm8
	movdqa xmm12, xmm9
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	paddd xmm1, xmm3
	paddd xmm2, xmm4
	pshufd xmm1, xmm1, 0x1b
	pshufd xmm2, xmm2, 0xb1
	movdqa xmm7, xmm1
	pblendw xmm7, xmm2, 0xf0
	palignr xmm2, xmm1, 8
	pshufb xmm7, xmm10
	pshufb xmm2, xmm10
	movdqu xmmword ptr [rdi + 0], xmm7
	movdqu xmmword ptr [rdi + 16], xmm2
	paddd xmm8, xmm11
	paddd xmm9, xmm12
	pshufd xmm8, xmm8, 0x1b
	pshufd xmm9, xmm9, 0xb1
	movdqa xmm7, xmm8
	pblendw xmm7, xmm9, 0xf0
	palignr xmm9, xmm8, 8
	pshufb xmm7, xmm10
	pshufb xmm9, xmm10
	movdqu xmmword ptr [rdi + 32], xmm7
	movdqu xmmword ptr [rdi + 48], xmm9
	add rsi, 128
	add rdx, 128
	add rdi, 64
	sub rcx, 1
	jnz .Lssz_sha256_shani_dual_pairs_3
.Lssz_sha256_shani_dual_pairs_466:
	ret
	.globl SYMBOL(ssz_sha256_shani_dual_columns)
	.p2align 6
SYMBOL(ssz_sha256_shani_dual_columns):
	test rcx, rcx
	jz .Lssz_sha256_shani_dual_columns_466
	movdqu xmm10, xmmword ptr [r8 + 9568]
.Lssz_sha256_shani_dual_columns_3:
	movdqu xmm3, xmmword ptr [rsi + 0]
	pshufb xmm3, xmm10
	movdqu xmm4, xmmword ptr [rsi + 16]
	pshufb xmm4, xmm10
	movdqu xmm5, xmmword ptr [rdx + 0]
	pshufb xmm5, xmm10
	movdqu xmm6, xmmword ptr [rdx + 16]
	pshufb xmm6, xmm10
	movdqu xmm1, xmmword ptr [r8 + 9536]
	movdqu xmm2, xmmword ptr [r8 + 9552]
	movdqu xmm11, xmmword ptr [rsi + 32]
	pshufb xmm11, xmm10
	movdqu xmm12, xmmword ptr [rsi + 48]
	pshufb xmm12, xmm10
	movdqu xmm13, xmmword ptr [rdx + 32]
	pshufb xmm13, xmm10
	movdqu xmm14, xmmword ptr [rdx + 48]
	pshufb xmm14, xmm10
	movdqu xmm8, xmmword ptr [r8 + 9536]
	movdqu xmm9, xmmword ptr [r8 + 9552]
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	paddd xmm1, xmmword ptr [r8 + 9536]
	paddd xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm3, xmm1
	movdqa xmm4, xmm2
	paddd xmm8, xmmword ptr [r8 + 9536]
	paddd xmm9, xmmword ptr [r8 + 9552]
	movdqa xmm11, xmm8
	movdqa xmm12, xmm9
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	paddd xmm1, xmm3
	paddd xmm2, xmm4
	pshufd xmm1, xmm1, 0x1b
	pshufd xmm2, xmm2, 0xb1
	movdqa xmm7, xmm1
	pblendw xmm7, xmm2, 0xf0
	palignr xmm2, xmm1, 8
	pshufb xmm7, xmm10
	pshufb xmm2, xmm10
	movdqu xmmword ptr [rdi + 0], xmm7
	movdqu xmmword ptr [rdi + 16], xmm2
	paddd xmm8, xmm11
	paddd xmm9, xmm12
	pshufd xmm8, xmm8, 0x1b
	pshufd xmm9, xmm9, 0xb1
	movdqa xmm7, xmm8
	pblendw xmm7, xmm9, 0xf0
	palignr xmm9, xmm8, 8
	pshufb xmm7, xmm10
	pshufb xmm9, xmm10
	movdqu xmmword ptr [rdi + 32], xmm7
	movdqu xmmword ptr [rdi + 48], xmm9
	add rsi, 64
	add rdx, 64
	add rdi, 64
	sub rcx, 1
	jnz .Lssz_sha256_shani_dual_columns_3
.Lssz_sha256_shani_dual_columns_466:
	ret
	.globl SYMBOL(ssz_sha256_shani_dual_fixed)
	.p2align 6
SYMBOL(ssz_sha256_shani_dual_fixed):
	test rcx, rcx
	jz .Lssz_sha256_shani_dual_fixed_466
	movdqu xmm10, xmmword ptr [r8 + 9568]
.Lssz_sha256_shani_dual_fixed_3:
	movdqu xmm3, xmmword ptr [rsi + 0]
	pshufb xmm3, xmm10
	movdqu xmm4, xmmword ptr [rsi + 16]
	pshufb xmm4, xmm10
	movdqu xmm5, xmmword ptr [rdx + 0]
	pshufb xmm5, xmm10
	movdqu xmm6, xmmword ptr [rdx + 16]
	pshufb xmm6, xmm10
	movdqu xmm1, xmmword ptr [r8 + 9536]
	movdqu xmm2, xmmword ptr [r8 + 9552]
	movdqu xmm11, xmmword ptr [rsi + 32]
	pshufb xmm11, xmm10
	movdqu xmm12, xmmword ptr [rsi + 48]
	pshufb xmm12, xmm10
	movdqu xmm13, xmmword ptr [rdx + 0]
	pshufb xmm13, xmm10
	movdqu xmm14, xmmword ptr [rdx + 16]
	pshufb xmm14, xmm10
	movdqu xmm8, xmmword ptr [r8 + 9536]
	movdqu xmm9, xmmword ptr [r8 + 9552]
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9024]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9040]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9056]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9072]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9088]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9104]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9120]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9136]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9152]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm11, xmm12
	movdqa xmm7, xmm14
	palignr xmm7, xmm13, 4
	paddd xmm11, xmm7
	sha256msg2 xmm11, xmm14
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9168]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm12, xmm13
	movdqa xmm7, xmm11
	palignr xmm7, xmm14, 4
	paddd xmm12, xmm7
	sha256msg2 xmm12, xmm11
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9184]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm13, xmm14
	movdqa xmm7, xmm12
	palignr xmm7, xmm11, 4
	paddd xmm13, xmm7
	sha256msg2 xmm13, xmm12
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9200]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	sha256msg1 xmm14, xmm11
	movdqa xmm7, xmm13
	palignr xmm7, xmm12, 4
	paddd xmm14, xmm7
	sha256msg2 xmm14, xmm13
	movdqa xmm0, xmm3
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm11
	paddd xmm0, xmmword ptr [r8 + 9216]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm4
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm12
	paddd xmm0, xmmword ptr [r8 + 9232]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm5
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm13
	paddd xmm0, xmmword ptr [r8 + 9248]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqa xmm0, xmm6
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqa xmm0, xmm14
	paddd xmm0, xmmword ptr [r8 + 9264]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	paddd xmm1, xmmword ptr [r8 + 9536]
	paddd xmm2, xmmword ptr [r8 + 9552]
	movdqa xmm3, xmm1
	movdqa xmm4, xmm2
	paddd xmm8, xmmword ptr [r8 + 9536]
	paddd xmm9, xmmword ptr [r8 + 9552]
	movdqa xmm11, xmm8
	movdqa xmm12, xmm9
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9280]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9296]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9312]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9328]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9344]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9360]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9376]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9392]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9408]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9424]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9440]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9456]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9472]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9488]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9504]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm0, xmmword ptr [r8 + 9520]
	sha256rnds2 xmm9, xmm8, xmm0
	pshufd xmm0, xmm0, 0x0e
	sha256rnds2 xmm8, xmm9, xmm0
	paddd xmm1, xmm3
	paddd xmm2, xmm4
	pshufd xmm1, xmm1, 0x1b
	pshufd xmm2, xmm2, 0xb1
	movdqa xmm7, xmm1
	pblendw xmm7, xmm2, 0xf0
	palignr xmm2, xmm1, 8
	pshufb xmm7, xmm10
	pshufb xmm2, xmm10
	movdqu xmmword ptr [rdi + 0], xmm7
	movdqu xmmword ptr [rdi + 16], xmm2
	paddd xmm8, xmm11
	paddd xmm9, xmm12
	pshufd xmm8, xmm8, 0x1b
	pshufd xmm9, xmm9, 0xb1
	movdqa xmm7, xmm8
	pblendw xmm7, xmm9, 0xf0
	palignr xmm9, xmm8, 8
	pshufb xmm7, xmm10
	pshufb xmm9, xmm10
	movdqu xmmword ptr [rdi + 32], xmm7
	movdqu xmmword ptr [rdi + 48], xmm9
	add rsi, 64
	add rdx, 0
	add rdi, 64
	sub rcx, 1
	jnz .Lssz_sha256_shani_dual_fixed_3
.Lssz_sha256_shani_dual_fixed_466:
	ret
	.globl SYMBOL(ssz_gather)
	.p2align 6
SYMBOL(ssz_gather):
	test rdx, rdx
	jz .Lssz_gather_11
	mov r10, rcx
	xor eax, eax
.Lssz_gather_4:
	mov rcx, r10
	rep movsb
	mov rcx, r9
	rep stosb
	add rsi, r8
	sub rdx, 1
	jnz .Lssz_gather_4
.Lssz_gather_11:
	ret
	.globl SYMBOL(ssz_gather_1)
	.p2align 6
SYMBOL(ssz_gather_1):
	test rdx, rdx
	jz .Lssz_gather_1_10
.Lssz_gather_1_2:
	movzx eax, byte ptr [rsi + 0]
	vmovd xmm0, eax
	vmovdqu ymmword ptr [rdi + 0], ymm0
	add rsi, r8
	add rsi, 1
	add rdi, 32
	sub rdx, 1
	jnz .Lssz_gather_1_2
.Lssz_gather_1_10:
	vzeroupper
	ret
	.globl SYMBOL(ssz_gather_2)
	.p2align 6
SYMBOL(ssz_gather_2):
	test rdx, rdx
	jz .Lssz_gather_2_10
.Lssz_gather_2_2:
	movzx eax, word ptr [rsi + 0]
	vmovd xmm0, eax
	vmovdqu ymmword ptr [rdi + 0], ymm0
	add rsi, r8
	add rsi, 2
	add rdi, 32
	sub rdx, 1
	jnz .Lssz_gather_2_2
.Lssz_gather_2_10:
	vzeroupper
	ret
	.globl SYMBOL(ssz_gather_4)
	.p2align 6
SYMBOL(ssz_gather_4):
	test rdx, rdx
	jz .Lssz_gather_4_9
.Lssz_gather_4_2:
	vmovd xmm0, dword ptr [rsi + 0]
	vmovdqu ymmword ptr [rdi + 0], ymm0
	add rsi, r8
	add rsi, 4
	add rdi, 32
	sub rdx, 1
	jnz .Lssz_gather_4_2
.Lssz_gather_4_9:
	vzeroupper
	ret
	.globl SYMBOL(ssz_gather_8)
	.p2align 6
SYMBOL(ssz_gather_8):
	test rdx, rdx
	jz .Lssz_gather_8_9
.Lssz_gather_8_2:
	vmovq xmm0, qword ptr [rsi + 0]
	vmovdqu ymmword ptr [rdi + 0], ymm0
	add rsi, r8
	add rsi, 8
	add rdi, 32
	sub rdx, 1
	jnz .Lssz_gather_8_2
.Lssz_gather_8_9:
	vzeroupper
	ret
	.globl SYMBOL(ssz_gather_16)
	.p2align 6
SYMBOL(ssz_gather_16):
	test rdx, rdx
	jz .Lssz_gather_16_9
.Lssz_gather_16_2:
	vmovdqu xmm0, xmmword ptr [rsi + 0]
	vmovdqu ymmword ptr [rdi + 0], ymm0
	add rsi, r8
	add rsi, 16
	add rdi, 32
	sub rdx, 1
	jnz .Lssz_gather_16_2
.Lssz_gather_16_9:
	vzeroupper
	ret
	.globl SYMBOL(ssz_gather_32)
	.p2align 6
SYMBOL(ssz_gather_32):
	test rdx, rdx
	jz .Lssz_gather_32_9
.Lssz_gather_32_2:
	vmovdqu ymm0, ymmword ptr [rsi + 0]
	vmovdqu ymmword ptr [rdi + 0], ymm0
	add rsi, r8
	add rsi, 32
	add rdi, 32
	sub rdx, 1
	jnz .Lssz_gather_32_2
.Lssz_gather_32_9:
	vzeroupper
	ret
	.globl SYMBOL(ssz_gather_key)
	.p2align 6
SYMBOL(ssz_gather_key):
	test rdx, rdx
	jz .Lssz_gather_key_11
.Lssz_gather_key_2:
	vmovdqu ymm0, ymmword ptr [rsi + 0]
	vmovdqu xmm1, xmmword ptr [rsi + 32]
	vmovdqu ymmword ptr [rdi + 0], ymm0
	vmovdqu ymmword ptr [rdi + 32], ymm1
	add rsi, r8
	add rsi, 48
	add rdi, 64
	sub rdx, 1
	jnz .Lssz_gather_key_2
.Lssz_gather_key_11:
	vzeroupper
	ret
#if defined(__APPLE__)
	.section __TEXT,__const
#else
	.section .rodata
#endif
	.globl SYMBOL(ssz_sha256_table)
	.p2align 6
SYMBOL(ssz_sha256_table):
	.byte 152, 47, 138, 66, 152, 47, 138, 66, 152, 47, 138, 66, 152, 47, 138, 66
	.byte 152, 47, 138, 66, 152, 47, 138, 66, 152, 47, 138, 66, 152, 47, 138, 66
	.byte 152, 47, 138, 66, 152, 47, 138, 66, 152, 47, 138, 66, 152, 47, 138, 66
	.byte 152, 47, 138, 66, 152, 47, 138, 66, 152, 47, 138, 66, 152, 47, 138, 66
	.byte 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113
	.byte 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113
	.byte 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113
	.byte 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113
	.byte 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181
	.byte 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181
	.byte 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181
	.byte 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181
	.byte 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233
	.byte 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233
	.byte 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233
	.byte 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233
	.byte 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57
	.byte 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57
	.byte 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57
	.byte 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57
	.byte 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89
	.byte 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89
	.byte 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89
	.byte 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89
	.byte 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146
	.byte 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146
	.byte 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146
	.byte 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146
	.byte 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171
	.byte 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171
	.byte 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171
	.byte 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171
	.byte 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216
	.byte 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216
	.byte 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216
	.byte 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216
	.byte 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18
	.byte 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18
	.byte 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18
	.byte 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18
	.byte 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36
	.byte 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36
	.byte 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36
	.byte 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36
	.byte 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85
	.byte 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85
	.byte 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85
	.byte 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85
	.byte 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114
	.byte 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114
	.byte 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114
	.byte 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114
	.byte 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128
	.byte 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128
	.byte 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128
	.byte 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128
	.byte 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155
	.byte 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155
	.byte 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155
	.byte 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155
	.byte 116, 241, 155, 193, 116, 241, 155, 193, 116, 241, 155, 193, 116, 241, 155, 193
	.byte 116, 241, 155, 193, 116, 241, 155, 193, 116, 241, 155, 193, 116, 241, 155, 193
	.byte 116, 241, 155, 193, 116, 241, 155, 193, 116, 241, 155, 193, 116, 241, 155, 193
	.byte 116, 241, 155, 193, 116, 241, 155, 193, 116, 241, 155, 193, 116, 241, 155, 193
	.byte 193, 105, 155, 228, 193, 105, 155, 228, 193, 105, 155, 228, 193, 105, 155, 228
	.byte 193, 105, 155, 228, 193, 105, 155, 228, 193, 105, 155, 228, 193, 105, 155, 228
	.byte 193, 105, 155, 228, 193, 105, 155, 228, 193, 105, 155, 228, 193, 105, 155, 228
	.byte 193, 105, 155, 228, 193, 105, 155, 228, 193, 105, 155, 228, 193, 105, 155, 228
	.byte 134, 71, 190, 239, 134, 71, 190, 239, 134, 71, 190, 239, 134, 71, 190, 239
	.byte 134, 71, 190, 239, 134, 71, 190, 239, 134, 71, 190, 239, 134, 71, 190, 239
	.byte 134, 71, 190, 239, 134, 71, 190, 239, 134, 71, 190, 239, 134, 71, 190, 239
	.byte 134, 71, 190, 239, 134, 71, 190, 239, 134, 71, 190, 239, 134, 71, 190, 239
	.byte 198, 157, 193, 15, 198, 157, 193, 15, 198, 157, 193, 15, 198, 157, 193, 15
	.byte 198, 157, 193, 15, 198, 157, 193, 15, 198, 157, 193, 15, 198, 157, 193, 15
	.byte 198, 157, 193, 15, 198, 157, 193, 15, 198, 157, 193, 15, 198, 157, 193, 15
	.byte 198, 157, 193, 15, 198, 157, 193, 15, 198, 157, 193, 15, 198, 157, 193, 15
	.byte 204, 161, 12, 36, 204, 161, 12, 36, 204, 161, 12, 36, 204, 161, 12, 36
	.byte 204, 161, 12, 36, 204, 161, 12, 36, 204, 161, 12, 36, 204, 161, 12, 36
	.byte 204, 161, 12, 36, 204, 161, 12, 36, 204, 161, 12, 36, 204, 161, 12, 36
	.byte 204, 161, 12, 36, 204, 161, 12, 36, 204, 161, 12, 36, 204, 161, 12, 36
	.byte 111, 44, 233, 45, 111, 44, 233, 45, 111, 44, 233, 45, 111, 44, 233, 45
	.byte 111, 44, 233, 45, 111, 44, 233, 45, 111, 44, 233, 45, 111, 44, 233, 45
	.byte 111, 44, 233, 45, 111, 44, 233, 45, 111, 44, 233, 45, 111, 44, 233, 45
	.byte 111, 44, 233, 45, 111, 44, 233, 45, 111, 44, 233, 45, 111, 44, 233, 45
	.byte 170, 132, 116, 74, 170, 132, 116, 74, 170, 132, 116, 74, 170, 132, 116, 74
	.byte 170, 132, 116, 74, 170, 132, 116, 74, 170, 132, 116, 74, 170, 132, 116, 74
	.byte 170, 132, 116, 74, 170, 132, 116, 74, 170, 132, 116, 74, 170, 132, 116, 74
	.byte 170, 132, 116, 74, 170, 132, 116, 74, 170, 132, 116, 74, 170, 132, 116, 74
	.byte 220, 169, 176, 92, 220, 169, 176, 92, 220, 169, 176, 92, 220, 169, 176, 92
	.byte 220, 169, 176, 92, 220, 169, 176, 92, 220, 169, 176, 92, 220, 169, 176, 92
	.byte 220, 169, 176, 92, 220, 169, 176, 92, 220, 169, 176, 92, 220, 169, 176, 92
	.byte 220, 169, 176, 92, 220, 169, 176, 92, 220, 169, 176, 92, 220, 169, 176, 92
	.byte 218, 136, 249, 118, 218, 136, 249, 118, 218, 136, 249, 118, 218, 136, 249, 118
	.byte 218, 136, 249, 118, 218, 136, 249, 118, 218, 136, 249, 118, 218, 136, 249, 118
	.byte 218, 136, 249, 118, 218, 136, 249, 118, 218, 136, 249, 118, 218, 136, 249, 118
	.byte 218, 136, 249, 118, 218, 136, 249, 118, 218, 136, 249, 118, 218, 136, 249, 118
	.byte 82, 81, 62, 152, 82, 81, 62, 152, 82, 81, 62, 152, 82, 81, 62, 152
	.byte 82, 81, 62, 152, 82, 81, 62, 152, 82, 81, 62, 152, 82, 81, 62, 152
	.byte 82, 81, 62, 152, 82, 81, 62, 152, 82, 81, 62, 152, 82, 81, 62, 152
	.byte 82, 81, 62, 152, 82, 81, 62, 152, 82, 81, 62, 152, 82, 81, 62, 152
	.byte 109, 198, 49, 168, 109, 198, 49, 168, 109, 198, 49, 168, 109, 198, 49, 168
	.byte 109, 198, 49, 168, 109, 198, 49, 168, 109, 198, 49, 168, 109, 198, 49, 168
	.byte 109, 198, 49, 168, 109, 198, 49, 168, 109, 198, 49, 168, 109, 198, 49, 168
	.byte 109, 198, 49, 168, 109, 198, 49, 168, 109, 198, 49, 168, 109, 198, 49, 168
	.byte 200, 39, 3, 176, 200, 39, 3, 176, 200, 39, 3, 176, 200, 39, 3, 176
	.byte 200, 39, 3, 176, 200, 39, 3, 176, 200, 39, 3, 176, 200, 39, 3, 176
	.byte 200, 39, 3, 176, 200, 39, 3, 176, 200, 39, 3, 176, 200, 39, 3, 176
	.byte 200, 39, 3, 176, 200, 39, 3, 176, 200, 39, 3, 176, 200, 39, 3, 176
	.byte 199, 127, 89, 191, 199, 127, 89, 191, 199, 127, 89, 191, 199, 127, 89, 191
	.byte 199, 127, 89, 191, 199, 127, 89, 191, 199, 127, 89, 191, 199, 127, 89, 191
	.byte 199, 127, 89, 191, 199, 127, 89, 191, 199, 127, 89, 191, 199, 127, 89, 191
	.byte 199, 127, 89, 191, 199, 127, 89, 191, 199, 127, 89, 191, 199, 127, 89, 191
	.byte 243, 11, 224, 198, 243, 11, 224, 198, 243, 11, 224, 198, 243, 11, 224, 198
	.byte 243, 11, 224, 198, 243, 11, 224, 198, 243, 11, 224, 198, 243, 11, 224, 198
	.byte 243, 11, 224, 198, 243, 11, 224, 198, 243, 11, 224, 198, 243, 11, 224, 198
	.byte 243, 11, 224, 198, 243, 11, 224, 198, 243, 11, 224, 198, 243, 11, 224, 198
	.byte 71, 145, 167, 213, 71, 145, 167, 213, 71, 145, 167, 213, 71, 145, 167, 213
	.byte 71, 145, 167, 213, 71, 145, 167, 213, 71, 145, 167, 213, 71, 145, 167, 213
	.byte 71, 145, 167, 213, 71, 145, 167, 213, 71, 145, 167, 213, 71, 145, 167, 213
	.byte 71, 145, 167, 213, 71, 145, 167, 213, 71, 145, 167, 213, 71, 145, 167, 213
	.byte 81, 99, 202, 6, 81, 99, 202, 6, 81, 99, 202, 6, 81, 99, 202, 6
	.byte 81, 99, 202, 6, 81, 99, 202, 6, 81, 99, 202, 6, 81, 99, 202, 6
	.byte 81, 99, 202, 6, 81, 99, 202, 6, 81, 99, 202, 6, 81, 99, 202, 6
	.byte 81, 99, 202, 6, 81, 99, 202, 6, 81, 99, 202, 6, 81, 99, 202, 6
	.byte 103, 41, 41, 20, 103, 41, 41, 20, 103, 41, 41, 20, 103, 41, 41, 20
	.byte 103, 41, 41, 20, 103, 41, 41, 20, 103, 41, 41, 20, 103, 41, 41, 20
	.byte 103, 41, 41, 20, 103, 41, 41, 20, 103, 41, 41, 20, 103, 41, 41, 20
	.byte 103, 41, 41, 20, 103, 41, 41, 20, 103, 41, 41, 20, 103, 41, 41, 20
	.byte 133, 10, 183, 39, 133, 10, 183, 39, 133, 10, 183, 39, 133, 10, 183, 39
	.byte 133, 10, 183, 39, 133, 10, 183, 39, 133, 10, 183, 39, 133, 10, 183, 39
	.byte 133, 10, 183, 39, 133, 10, 183, 39, 133, 10, 183, 39, 133, 10, 183, 39
	.byte 133, 10, 183, 39, 133, 10, 183, 39, 133, 10, 183, 39, 133, 10, 183, 39
	.byte 56, 33, 27, 46, 56, 33, 27, 46, 56, 33, 27, 46, 56, 33, 27, 46
	.byte 56, 33, 27, 46, 56, 33, 27, 46, 56, 33, 27, 46, 56, 33, 27, 46
	.byte 56, 33, 27, 46, 56, 33, 27, 46, 56, 33, 27, 46, 56, 33, 27, 46
	.byte 56, 33, 27, 46, 56, 33, 27, 46, 56, 33, 27, 46, 56, 33, 27, 46
	.byte 252, 109, 44, 77, 252, 109, 44, 77, 252, 109, 44, 77, 252, 109, 44, 77
	.byte 252, 109, 44, 77, 252, 109, 44, 77, 252, 109, 44, 77, 252, 109, 44, 77
	.byte 252, 109, 44, 77, 252, 109, 44, 77, 252, 109, 44, 77, 252, 109, 44, 77
	.byte 252, 109, 44, 77, 252, 109, 44, 77, 252, 109, 44, 77, 252, 109, 44, 77
	.byte 19, 13, 56, 83, 19, 13, 56, 83, 19, 13, 56, 83, 19, 13, 56, 83
	.byte 19, 13, 56, 83, 19, 13, 56, 83, 19, 13, 56, 83, 19, 13, 56, 83
	.byte 19, 13, 56, 83, 19, 13, 56, 83, 19, 13, 56, 83, 19, 13, 56, 83
	.byte 19, 13, 56, 83, 19, 13, 56, 83, 19, 13, 56, 83, 19, 13, 56, 83
	.byte 84, 115, 10, 101, 84, 115, 10, 101, 84, 115, 10, 101, 84, 115, 10, 101
	.byte 84, 115, 10, 101, 84, 115, 10, 101, 84, 115, 10, 101, 84, 115, 10, 101
	.byte 84, 115, 10, 101, 84, 115, 10, 101, 84, 115, 10, 101, 84, 115, 10, 101
	.byte 84, 115, 10, 101, 84, 115, 10, 101, 84, 115, 10, 101, 84, 115, 10, 101
	.byte 187, 10, 106, 118, 187, 10, 106, 118, 187, 10, 106, 118, 187, 10, 106, 118
	.byte 187, 10, 106, 118, 187, 10, 106, 118, 187, 10, 106, 118, 187, 10, 106, 118
	.byte 187, 10, 106, 118, 187, 10, 106, 118, 187, 10, 106, 118, 187, 10, 106, 118
	.byte 187, 10, 106, 118, 187, 10, 106, 118, 187, 10, 106, 118, 187, 10, 106, 118
	.byte 46, 201, 194, 129, 46, 201, 194, 129, 46, 201, 194, 129, 46, 201, 194, 129
	.byte 46, 201, 194, 129, 46, 201, 194, 129, 46, 201, 194, 129, 46, 201, 194, 129
	.byte 46, 201, 194, 129, 46, 201, 194, 129, 46, 201, 194, 129, 46, 201, 194, 129
	.byte 46, 201, 194, 129, 46, 201, 194, 129, 46, 201, 194, 129, 46, 201, 194, 129
	.byte 133, 44, 114, 146, 133, 44, 114, 146, 133, 44, 114, 146, 133, 44, 114, 146
	.byte 133, 44, 114, 146, 133, 44, 114, 146, 133, 44, 114, 146, 133, 44, 114, 146
	.byte 133, 44, 114, 146, 133, 44, 114, 146, 133, 44, 114, 146, 133, 44, 114, 146
	.byte 133, 44, 114, 146, 133, 44, 114, 146, 133, 44, 114, 146, 133, 44, 114, 146
	.byte 161, 232, 191, 162, 161, 232, 191, 162, 161, 232, 191, 162, 161, 232, 191, 162
	.byte 161, 232, 191, 162, 161, 232, 191, 162, 161, 232, 191, 162, 161, 232, 191, 162
	.byte 161, 232, 191, 162, 161, 232, 191, 162, 161, 232, 191, 162, 161, 232, 191, 162
	.byte 161, 232, 191, 162, 161, 232, 191, 162, 161, 232, 191, 162, 161, 232, 191, 162
	.byte 75, 102, 26, 168, 75, 102, 26, 168, 75, 102, 26, 168, 75, 102, 26, 168
	.byte 75, 102, 26, 168, 75, 102, 26, 168, 75, 102, 26, 168, 75, 102, 26, 168
	.byte 75, 102, 26, 168, 75, 102, 26, 168, 75, 102, 26, 168, 75, 102, 26, 168
	.byte 75, 102, 26, 168, 75, 102, 26, 168, 75, 102, 26, 168, 75, 102, 26, 168
	.byte 112, 139, 75, 194, 112, 139, 75, 194, 112, 139, 75, 194, 112, 139, 75, 194
	.byte 112, 139, 75, 194, 112, 139, 75, 194, 112, 139, 75, 194, 112, 139, 75, 194
	.byte 112, 139, 75, 194, 112, 139, 75, 194, 112, 139, 75, 194, 112, 139, 75, 194
	.byte 112, 139, 75, 194, 112, 139, 75, 194, 112, 139, 75, 194, 112, 139, 75, 194
	.byte 163, 81, 108, 199, 163, 81, 108, 199, 163, 81, 108, 199, 163, 81, 108, 199
	.byte 163, 81, 108, 199, 163, 81, 108, 199, 163, 81, 108, 199, 163, 81, 108, 199
	.byte 163, 81, 108, 199, 163, 81, 108, 199, 163, 81, 108, 199, 163, 81, 108, 199
	.byte 163, 81, 108, 199, 163, 81, 108, 199, 163, 81, 108, 199, 163, 81, 108, 199
	.byte 25, 232, 146, 209, 25, 232, 146, 209, 25, 232, 146, 209, 25, 232, 146, 209
	.byte 25, 232, 146, 209, 25, 232, 146, 209, 25, 232, 146, 209, 25, 232, 146, 209
	.byte 25, 232, 146, 209, 25, 232, 146, 209, 25, 232, 146, 209, 25, 232, 146, 209
	.byte 25, 232, 146, 209, 25, 232, 146, 209, 25, 232, 146, 209, 25, 232, 146, 209
	.byte 36, 6, 153, 214, 36, 6, 153, 214, 36, 6, 153, 214, 36, 6, 153, 214
	.byte 36, 6, 153, 214, 36, 6, 153, 214, 36, 6, 153, 214, 36, 6, 153, 214
	.byte 36, 6, 153, 214, 36, 6, 153, 214, 36, 6, 153, 214, 36, 6, 153, 214
	.byte 36, 6, 153, 214, 36, 6, 153, 214, 36, 6, 153, 214, 36, 6, 153, 214
	.byte 133, 53, 14, 244, 133, 53, 14, 244, 133, 53, 14, 244, 133, 53, 14, 244
	.byte 133, 53, 14, 244, 133, 53, 14, 244, 133, 53, 14, 244, 133, 53, 14, 244
	.byte 133, 53, 14, 244, 133, 53, 14, 244, 133, 53, 14, 244, 133, 53, 14, 244
	.byte 133, 53, 14, 244, 133, 53, 14, 244, 133, 53, 14, 244, 133, 53, 14, 244
	.byte 112, 160, 106, 16, 112, 160, 106, 16, 112, 160, 106, 16, 112, 160, 106, 16
	.byte 112, 160, 106, 16, 112, 160, 106, 16, 112, 160, 106, 16, 112, 160, 106, 16
	.byte 112, 160, 106, 16, 112, 160, 106, 16, 112, 160, 106, 16, 112, 160, 106, 16
	.byte 112, 160, 106, 16, 112, 160, 106, 16, 112, 160, 106, 16, 112, 160, 106, 16
	.byte 22, 193, 164, 25, 22, 193, 164, 25, 22, 193, 164, 25, 22, 193, 164, 25
	.byte 22, 193, 164, 25, 22, 193, 164, 25, 22, 193, 164, 25, 22, 193, 164, 25
	.byte 22, 193, 164, 25, 22, 193, 164, 25, 22, 193, 164, 25, 22, 193, 164, 25
	.byte 22, 193, 164, 25, 22, 193, 164, 25, 22, 193, 164, 25, 22, 193, 164, 25
	.byte 8, 108, 55, 30, 8, 108, 55, 30, 8, 108, 55, 30, 8, 108, 55, 30
	.byte 8, 108, 55, 30, 8, 108, 55, 30, 8, 108, 55, 30, 8, 108, 55, 30
	.byte 8, 108, 55, 30, 8, 108, 55, 30, 8, 108, 55, 30, 8, 108, 55, 30
	.byte 8, 108, 55, 30, 8, 108, 55, 30, 8, 108, 55, 30, 8, 108, 55, 30
	.byte 76, 119, 72, 39, 76, 119, 72, 39, 76, 119, 72, 39, 76, 119, 72, 39
	.byte 76, 119, 72, 39, 76, 119, 72, 39, 76, 119, 72, 39, 76, 119, 72, 39
	.byte 76, 119, 72, 39, 76, 119, 72, 39, 76, 119, 72, 39, 76, 119, 72, 39
	.byte 76, 119, 72, 39, 76, 119, 72, 39, 76, 119, 72, 39, 76, 119, 72, 39
	.byte 181, 188, 176, 52, 181, 188, 176, 52, 181, 188, 176, 52, 181, 188, 176, 52
	.byte 181, 188, 176, 52, 181, 188, 176, 52, 181, 188, 176, 52, 181, 188, 176, 52
	.byte 181, 188, 176, 52, 181, 188, 176, 52, 181, 188, 176, 52, 181, 188, 176, 52
	.byte 181, 188, 176, 52, 181, 188, 176, 52, 181, 188, 176, 52, 181, 188, 176, 52
	.byte 179, 12, 28, 57, 179, 12, 28, 57, 179, 12, 28, 57, 179, 12, 28, 57
	.byte 179, 12, 28, 57, 179, 12, 28, 57, 179, 12, 28, 57, 179, 12, 28, 57
	.byte 179, 12, 28, 57, 179, 12, 28, 57, 179, 12, 28, 57, 179, 12, 28, 57
	.byte 179, 12, 28, 57, 179, 12, 28, 57, 179, 12, 28, 57, 179, 12, 28, 57
	.byte 74, 170, 216, 78, 74, 170, 216, 78, 74, 170, 216, 78, 74, 170, 216, 78
	.byte 74, 170, 216, 78, 74, 170, 216, 78, 74, 170, 216, 78, 74, 170, 216, 78
	.byte 74, 170, 216, 78, 74, 170, 216, 78, 74, 170, 216, 78, 74, 170, 216, 78
	.byte 74, 170, 216, 78, 74, 170, 216, 78, 74, 170, 216, 78, 74, 170, 216, 78
	.byte 79, 202, 156, 91, 79, 202, 156, 91, 79, 202, 156, 91, 79, 202, 156, 91
	.byte 79, 202, 156, 91, 79, 202, 156, 91, 79, 202, 156, 91, 79, 202, 156, 91
	.byte 79, 202, 156, 91, 79, 202, 156, 91, 79, 202, 156, 91, 79, 202, 156, 91
	.byte 79, 202, 156, 91, 79, 202, 156, 91, 79, 202, 156, 91, 79, 202, 156, 91
	.byte 243, 111, 46, 104, 243, 111, 46, 104, 243, 111, 46, 104, 243, 111, 46, 104
	.byte 243, 111, 46, 104, 243, 111, 46, 104, 243, 111, 46, 104, 243, 111, 46, 104
	.byte 243, 111, 46, 104, 243, 111, 46, 104, 243, 111, 46, 104, 243, 111, 46, 104
	.byte 243, 111, 46, 104, 243, 111, 46, 104, 243, 111, 46, 104, 243, 111, 46, 104
	.byte 238, 130, 143, 116, 238, 130, 143, 116, 238, 130, 143, 116, 238, 130, 143, 116
	.byte 238, 130, 143, 116, 238, 130, 143, 116, 238, 130, 143, 116, 238, 130, 143, 116
	.byte 238, 130, 143, 116, 238, 130, 143, 116, 238, 130, 143, 116, 238, 130, 143, 116
	.byte 238, 130, 143, 116, 238, 130, 143, 116, 238, 130, 143, 116, 238, 130, 143, 116
	.byte 111, 99, 165, 120, 111, 99, 165, 120, 111, 99, 165, 120, 111, 99, 165, 120
	.byte 111, 99, 165, 120, 111, 99, 165, 120, 111, 99, 165, 120, 111, 99, 165, 120
	.byte 111, 99, 165, 120, 111, 99, 165, 120, 111, 99, 165, 120, 111, 99, 165, 120
	.byte 111, 99, 165, 120, 111, 99, 165, 120, 111, 99, 165, 120, 111, 99, 165, 120
	.byte 20, 120, 200, 132, 20, 120, 200, 132, 20, 120, 200, 132, 20, 120, 200, 132
	.byte 20, 120, 200, 132, 20, 120, 200, 132, 20, 120, 200, 132, 20, 120, 200, 132
	.byte 20, 120, 200, 132, 20, 120, 200, 132, 20, 120, 200, 132, 20, 120, 200, 132
	.byte 20, 120, 200, 132, 20, 120, 200, 132, 20, 120, 200, 132, 20, 120, 200, 132
	.byte 8, 2, 199, 140, 8, 2, 199, 140, 8, 2, 199, 140, 8, 2, 199, 140
	.byte 8, 2, 199, 140, 8, 2, 199, 140, 8, 2, 199, 140, 8, 2, 199, 140
	.byte 8, 2, 199, 140, 8, 2, 199, 140, 8, 2, 199, 140, 8, 2, 199, 140
	.byte 8, 2, 199, 140, 8, 2, 199, 140, 8, 2, 199, 140, 8, 2, 199, 140
	.byte 250, 255, 190, 144, 250, 255, 190, 144, 250, 255, 190, 144, 250, 255, 190, 144
	.byte 250, 255, 190, 144, 250, 255, 190, 144, 250, 255, 190, 144, 250, 255, 190, 144
	.byte 250, 255, 190, 144, 250, 255, 190, 144, 250, 255, 190, 144, 250, 255, 190, 144
	.byte 250, 255, 190, 144, 250, 255, 190, 144, 250, 255, 190, 144, 250, 255, 190, 144
	.byte 235, 108, 80, 164, 235, 108, 80, 164, 235, 108, 80, 164, 235, 108, 80, 164
	.byte 235, 108, 80, 164, 235, 108, 80, 164, 235, 108, 80, 164, 235, 108, 80, 164
	.byte 235, 108, 80, 164, 235, 108, 80, 164, 235, 108, 80, 164, 235, 108, 80, 164
	.byte 235, 108, 80, 164, 235, 108, 80, 164, 235, 108, 80, 164, 235, 108, 80, 164
	.byte 247, 163, 249, 190, 247, 163, 249, 190, 247, 163, 249, 190, 247, 163, 249, 190
	.byte 247, 163, 249, 190, 247, 163, 249, 190, 247, 163, 249, 190, 247, 163, 249, 190
	.byte 247, 163, 249, 190, 247, 163, 249, 190, 247, 163, 249, 190, 247, 163, 249, 190
	.byte 247, 163, 249, 190, 247, 163, 249, 190, 247, 163, 249, 190, 247, 163, 249, 190
	.byte 242, 120, 113, 198, 242, 120, 113, 198, 242, 120, 113, 198, 242, 120, 113, 198
	.byte 242, 120, 113, 198, 242, 120, 113, 198, 242, 120, 113, 198, 242, 120, 113, 198
	.byte 242, 120, 113, 198, 242, 120, 113, 198, 242, 120, 113, 198, 242, 120, 113, 198
	.byte 242, 120, 113, 198, 242, 120, 113, 198, 242, 120, 113, 198, 242, 120, 113, 198
	.byte 152, 47, 138, 194, 152, 47, 138, 194, 152, 47, 138, 194, 152, 47, 138, 194
	.byte 152, 47, 138, 194, 152, 47, 138, 194, 152, 47, 138, 194, 152, 47, 138, 194
	.byte 152, 47, 138, 194, 152, 47, 138, 194, 152, 47, 138, 194, 152, 47, 138, 194
	.byte 152, 47, 138, 194, 152, 47, 138, 194, 152, 47, 138, 194, 152, 47, 138, 194
	.byte 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113
	.byte 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113
	.byte 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113
	.byte 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113, 145, 68, 55, 113
	.byte 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181
	.byte 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181
	.byte 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181
	.byte 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181, 207, 251, 192, 181
	.byte 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233
	.byte 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233
	.byte 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233
	.byte 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233, 165, 219, 181, 233
	.byte 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57
	.byte 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57
	.byte 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57
	.byte 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57, 91, 194, 86, 57
	.byte 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89
	.byte 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89
	.byte 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89
	.byte 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89, 241, 17, 241, 89
	.byte 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146
	.byte 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146
	.byte 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146
	.byte 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146, 164, 130, 63, 146
	.byte 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171
	.byte 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171
	.byte 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171
	.byte 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171, 213, 94, 28, 171
	.byte 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216
	.byte 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216
	.byte 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216
	.byte 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216, 152, 170, 7, 216
	.byte 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18
	.byte 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18
	.byte 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18
	.byte 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18, 1, 91, 131, 18
	.byte 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36
	.byte 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36
	.byte 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36
	.byte 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36, 190, 133, 49, 36
	.byte 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85
	.byte 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85
	.byte 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85
	.byte 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85, 195, 125, 12, 85
	.byte 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114
	.byte 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114
	.byte 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114
	.byte 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114, 116, 93, 190, 114
	.byte 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128
	.byte 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128
	.byte 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128
	.byte 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128, 254, 177, 222, 128
	.byte 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155
	.byte 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155
	.byte 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155
	.byte 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155, 167, 6, 220, 155
	.byte 116, 243, 155, 193, 116, 243, 155, 193, 116, 243, 155, 193, 116, 243, 155, 193
	.byte 116, 243, 155, 193, 116, 243, 155, 193, 116, 243, 155, 193, 116, 243, 155, 193
	.byte 116, 243, 155, 193, 116, 243, 155, 193, 116, 243, 155, 193, 116, 243, 155, 193
	.byte 116, 243, 155, 193, 116, 243, 155, 193, 116, 243, 155, 193, 116, 243, 155, 193
	.byte 193, 105, 155, 100, 193, 105, 155, 100, 193, 105, 155, 100, 193, 105, 155, 100
	.byte 193, 105, 155, 100, 193, 105, 155, 100, 193, 105, 155, 100, 193, 105, 155, 100
	.byte 193, 105, 155, 100, 193, 105, 155, 100, 193, 105, 155, 100, 193, 105, 155, 100
	.byte 193, 105, 155, 100, 193, 105, 155, 100, 193, 105, 155, 100, 193, 105, 155, 100
	.byte 134, 71, 254, 240, 134, 71, 254, 240, 134, 71, 254, 240, 134, 71, 254, 240
	.byte 134, 71, 254, 240, 134, 71, 254, 240, 134, 71, 254, 240, 134, 71, 254, 240
	.byte 134, 71, 254, 240, 134, 71, 254, 240, 134, 71, 254, 240, 134, 71, 254, 240
	.byte 134, 71, 254, 240, 134, 71, 254, 240, 134, 71, 254, 240, 134, 71, 254, 240
	.byte 198, 237, 225, 15, 198, 237, 225, 15, 198, 237, 225, 15, 198, 237, 225, 15
	.byte 198, 237, 225, 15, 198, 237, 225, 15, 198, 237, 225, 15, 198, 237, 225, 15
	.byte 198, 237, 225, 15, 198, 237, 225, 15, 198, 237, 225, 15, 198, 237, 225, 15
	.byte 198, 237, 225, 15, 198, 237, 225, 15, 198, 237, 225, 15, 198, 237, 225, 15
	.byte 84, 242, 12, 36, 84, 242, 12, 36, 84, 242, 12, 36, 84, 242, 12, 36
	.byte 84, 242, 12, 36, 84, 242, 12, 36, 84, 242, 12, 36, 84, 242, 12, 36
	.byte 84, 242, 12, 36, 84, 242, 12, 36, 84, 242, 12, 36, 84, 242, 12, 36
	.byte 84, 242, 12, 36, 84, 242, 12, 36, 84, 242, 12, 36, 84, 242, 12, 36
	.byte 111, 52, 233, 79, 111, 52, 233, 79, 111, 52, 233, 79, 111, 52, 233, 79
	.byte 111, 52, 233, 79, 111, 52, 233, 79, 111, 52, 233, 79, 111, 52, 233, 79
	.byte 111, 52, 233, 79, 111, 52, 233, 79, 111, 52, 233, 79, 111, 52, 233, 79
	.byte 111, 52, 233, 79, 111, 52, 233, 79, 111, 52, 233, 79, 111, 52, 233, 79
	.byte 190, 132, 201, 108, 190, 132, 201, 108, 190, 132, 201, 108, 190, 132, 201, 108
	.byte 190, 132, 201, 108, 190, 132, 201, 108, 190, 132, 201, 108, 190, 132, 201, 108
	.byte 190, 132, 201, 108, 190, 132, 201, 108, 190, 132, 201, 108, 190, 132, 201, 108
	.byte 190, 132, 201, 108, 190, 132, 201, 108, 190, 132, 201, 108, 190, 132, 201, 108
	.byte 30, 65, 185, 97, 30, 65, 185, 97, 30, 65, 185, 97, 30, 65, 185, 97
	.byte 30, 65, 185, 97, 30, 65, 185, 97, 30, 65, 185, 97, 30, 65, 185, 97
	.byte 30, 65, 185, 97, 30, 65, 185, 97, 30, 65, 185, 97, 30, 65, 185, 97
	.byte 30, 65, 185, 97, 30, 65, 185, 97, 30, 65, 185, 97, 30, 65, 185, 97
	.byte 250, 136, 249, 22, 250, 136, 249, 22, 250, 136, 249, 22, 250, 136, 249, 22
	.byte 250, 136, 249, 22, 250, 136, 249, 22, 250, 136, 249, 22, 250, 136, 249, 22
	.byte 250, 136, 249, 22, 250, 136, 249, 22, 250, 136, 249, 22, 250, 136, 249, 22
	.byte 250, 136, 249, 22, 250, 136, 249, 22, 250, 136, 249, 22, 250, 136, 249, 22
	.byte 82, 81, 198, 242, 82, 81, 198, 242, 82, 81, 198, 242, 82, 81, 198, 242
	.byte 82, 81, 198, 242, 82, 81, 198, 242, 82, 81, 198, 242, 82, 81, 198, 242
	.byte 82, 81, 198, 242, 82, 81, 198, 242, 82, 81, 198, 242, 82, 81, 198, 242
	.byte 82, 81, 198, 242, 82, 81, 198, 242, 82, 81, 198, 242, 82, 81, 198, 242
	.byte 109, 90, 142, 168, 109, 90, 142, 168, 109, 90, 142, 168, 109, 90, 142, 168
	.byte 109, 90, 142, 168, 109, 90, 142, 168, 109, 90, 142, 168, 109, 90, 142, 168
	.byte 109, 90, 142, 168, 109, 90, 142, 168, 109, 90, 142, 168, 109, 90, 142, 168
	.byte 109, 90, 142, 168, 109, 90, 142, 168, 109, 90, 142, 168, 109, 90, 142, 168
	.byte 101, 252, 25, 176, 101, 252, 25, 176, 101, 252, 25, 176, 101, 252, 25, 176
	.byte 101, 252, 25, 176, 101, 252, 25, 176, 101, 252, 25, 176, 101, 252, 25, 176
	.byte 101, 252, 25, 176, 101, 252, 25, 176, 101, 252, 25, 176, 101, 252, 25, 176
	.byte 101, 252, 25, 176, 101, 252, 25, 176, 101, 252, 25, 176, 101, 252, 25, 176
	.byte 199, 158, 217, 185, 199, 158, 217, 185, 199, 158, 217, 185, 199, 158, 217, 185
	.byte 199, 158, 217, 185, 199, 158, 217, 185, 199, 158, 217, 185, 199, 158, 217, 185
	.byte 199, 158, 217, 185, 199, 158, 217, 185, 199, 158, 217, 185, 199, 158, 217, 185
	.byte 199, 158, 217, 185, 199, 158, 217, 185, 199, 158, 217, 185, 199, 158, 217, 185
	.byte 195, 49, 18, 154, 195, 49, 18, 154, 195, 49, 18, 154, 195, 49, 18, 154
	.byte 195, 49, 18, 154, 195, 49, 18, 154, 195, 49, 18, 154, 195, 49, 18, 154
	.byte 195, 49, 18, 154, 195, 49, 18, 154, 195, 49, 18, 154, 195, 49, 18, 154
	.byte 195, 49, 18, 154, 195, 49, 18, 154, 195, 49, 18, 154, 195, 49, 18, 154
	.byte 160, 234, 14, 231, 160, 234, 14, 231, 160, 234, 14, 231, 160, 234, 14, 231
	.byte 160, 234, 14, 231, 160, 234, 14, 231, 160, 234, 14, 231, 160, 234, 14, 231
	.byte 160, 234, 14, 231, 160, 234, 14, 231, 160, 234, 14, 231, 160, 234, 14, 231
	.byte 160, 234, 14, 231, 160, 234, 14, 231, 160, 234, 14, 231, 160, 234, 14, 231
	.byte 43, 35, 177, 253, 43, 35, 177, 253, 43, 35, 177, 253, 43, 35, 177, 253
	.byte 43, 35, 177, 253, 43, 35, 177, 253, 43, 35, 177, 253, 43, 35, 177, 253
	.byte 43, 35, 177, 253, 43, 35, 177, 253, 43, 35, 177, 253, 43, 35, 177, 253
	.byte 43, 35, 177, 253, 43, 35, 177, 253, 43, 35, 177, 253, 43, 35, 177, 253
	.byte 176, 62, 53, 199, 176, 62, 53, 199, 176, 62, 53, 199, 176, 62, 53, 199
	.byte 176, 62, 53, 199, 176, 62, 53, 199, 176, 62, 53, 199, 176, 62, 53, 199
	.byte 176, 62, 53, 199, 176, 62, 53, 199, 176, 62, 53, 199, 176, 62, 53, 199
	.byte 176, 62, 53, 199, 176, 62, 53, 199, 176, 62, 53, 199, 176, 62, 53, 199
	.byte 213, 186, 105, 48, 213, 186, 105, 48, 213, 186, 105, 48, 213, 186, 105, 48
	.byte 213, 186, 105, 48, 213, 186, 105, 48, 213, 186, 105, 48, 213, 186, 105, 48
	.byte 213, 186, 105, 48, 213, 186, 105, 48, 213, 186, 105, 48, 213, 186, 105, 48
	.byte 213, 186, 105, 48, 213, 186, 105, 48, 213, 186, 105, 48, 213, 186, 105, 48
	.byte 95, 109, 151, 203, 95, 109, 151, 203, 95, 109, 151, 203, 95, 109, 151, 203
	.byte 95, 109, 151, 203, 95, 109, 151, 203, 95, 109, 151, 203, 95, 109, 151, 203
	.byte 95, 109, 151, 203, 95, 109, 151, 203, 95, 109, 151, 203, 95, 109, 151, 203
	.byte 95, 109, 151, 203, 95, 109, 151, 203, 95, 109, 151, 203, 95, 109, 151, 203
	.byte 143, 17, 15, 90, 143, 17, 15, 90, 143, 17, 15, 90, 143, 17, 15, 90
	.byte 143, 17, 15, 90, 143, 17, 15, 90, 143, 17, 15, 90, 143, 17, 15, 90
	.byte 143, 17, 15, 90, 143, 17, 15, 90, 143, 17, 15, 90, 143, 17, 15, 90
	.byte 143, 17, 15, 90, 143, 17, 15, 90, 143, 17, 15, 90, 143, 17, 15, 90
	.byte 253, 238, 30, 220, 253, 238, 30, 220, 253, 238, 30, 220, 253, 238, 30, 220
	.byte 253, 238, 30, 220, 253, 238, 30, 220, 253, 238, 30, 220, 253, 238, 30, 220
	.byte 253, 238, 30, 220, 253, 238, 30, 220, 253, 238, 30, 220, 253, 238, 30, 220
	.byte 253, 238, 30, 220, 253, 238, 30, 220, 253, 238, 30, 220, 253, 238, 30, 220
	.byte 137, 182, 53, 10, 137, 182, 53, 10, 137, 182, 53, 10, 137, 182, 53, 10
	.byte 137, 182, 53, 10, 137, 182, 53, 10, 137, 182, 53, 10, 137, 182, 53, 10
	.byte 137, 182, 53, 10, 137, 182, 53, 10, 137, 182, 53, 10, 137, 182, 53, 10
	.byte 137, 182, 53, 10, 137, 182, 53, 10, 137, 182, 53, 10, 137, 182, 53, 10
	.byte 4, 122, 11, 222, 4, 122, 11, 222, 4, 122, 11, 222, 4, 122, 11, 222
	.byte 4, 122, 11, 222, 4, 122, 11, 222, 4, 122, 11, 222, 4, 122, 11, 222
	.byte 4, 122, 11, 222, 4, 122, 11, 222, 4, 122, 11, 222, 4, 122, 11, 222
	.byte 4, 122, 11, 222, 4, 122, 11, 222, 4, 122, 11, 222, 4, 122, 11, 222
	.byte 157, 202, 244, 88, 157, 202, 244, 88, 157, 202, 244, 88, 157, 202, 244, 88
	.byte 157, 202, 244, 88, 157, 202, 244, 88, 157, 202, 244, 88, 157, 202, 244, 88
	.byte 157, 202, 244, 88, 157, 202, 244, 88, 157, 202, 244, 88, 157, 202, 244, 88
	.byte 157, 202, 244, 88, 157, 202, 244, 88, 157, 202, 244, 88, 157, 202, 244, 88
	.byte 22, 91, 93, 225, 22, 91, 93, 225, 22, 91, 93, 225, 22, 91, 93, 225
	.byte 22, 91, 93, 225, 22, 91, 93, 225, 22, 91, 93, 225, 22, 91, 93, 225
	.byte 22, 91, 93, 225, 22, 91, 93, 225, 22, 91, 93, 225, 22, 91, 93, 225
	.byte 22, 91, 93, 225, 22, 91, 93, 225, 22, 91, 93, 225, 22, 91, 93, 225
	.byte 134, 62, 127, 0, 134, 62, 127, 0, 134, 62, 127, 0, 134, 62, 127, 0
	.byte 134, 62, 127, 0, 134, 62, 127, 0, 134, 62, 127, 0, 134, 62, 127, 0
	.byte 134, 62, 127, 0, 134, 62, 127, 0, 134, 62, 127, 0, 134, 62, 127, 0
	.byte 134, 62, 127, 0, 134, 62, 127, 0, 134, 62, 127, 0, 134, 62, 127, 0
	.byte 128, 137, 8, 55, 128, 137, 8, 55, 128, 137, 8, 55, 128, 137, 8, 55
	.byte 128, 137, 8, 55, 128, 137, 8, 55, 128, 137, 8, 55, 128, 137, 8, 55
	.byte 128, 137, 8, 55, 128, 137, 8, 55, 128, 137, 8, 55, 128, 137, 8, 55
	.byte 128, 137, 8, 55, 128, 137, 8, 55, 128, 137, 8, 55, 128, 137, 8, 55
	.byte 50, 234, 7, 165, 50, 234, 7, 165, 50, 234, 7, 165, 50, 234, 7, 165
	.byte 50, 234, 7, 165, 50, 234, 7, 165, 50, 234, 7, 165, 50, 234, 7, 165
	.byte 50, 234, 7, 165, 50, 234, 7, 165, 50, 234, 7, 165, 50, 234, 7, 165
	.byte 50, 234, 7, 165, 50, 234, 7, 165, 50, 234, 7, 165, 50, 234, 7, 165
	.byte 55, 149, 171, 111, 55, 149, 171, 111, 55, 149, 171, 111, 55, 149, 171, 111
	.byte 55, 149, 171, 111, 55, 149, 171, 111, 55, 149, 171, 111, 55, 149, 171, 111
	.byte 55, 149, 171, 111, 55, 149, 171, 111, 55, 149, 171, 111, 55, 149, 171, 111
	.byte 55, 149, 171, 111, 55, 149, 171, 111, 55, 149, 171, 111, 55, 149, 171, 111
	.byte 16, 97, 64, 23, 16, 97, 64, 23, 16, 97, 64, 23, 16, 97, 64, 23
	.byte 16, 97, 64, 23, 16, 97, 64, 23, 16, 97, 64, 23, 16, 97, 64, 23
	.byte 16, 97, 64, 23, 16, 97, 64, 23, 16, 97, 64, 23, 16, 97, 64, 23
	.byte 16, 97, 64, 23, 16, 97, 64, 23, 16, 97, 64, 23, 16, 97, 64, 23
	.byte 241, 214, 140, 13, 241, 214, 140, 13, 241, 214, 140, 13, 241, 214, 140, 13
	.byte 241, 214, 140, 13, 241, 214, 140, 13, 241, 214, 140, 13, 241, 214, 140, 13
	.byte 241, 214, 140, 13, 241, 214, 140, 13, 241, 214, 140, 13, 241, 214, 140, 13
	.byte 241, 214, 140, 13, 241, 214, 140, 13, 241, 214, 140, 13, 241, 214, 140, 13
	.byte 109, 59, 170, 205, 109, 59, 170, 205, 109, 59, 170, 205, 109, 59, 170, 205
	.byte 109, 59, 170, 205, 109, 59, 170, 205, 109, 59, 170, 205, 109, 59, 170, 205
	.byte 109, 59, 170, 205, 109, 59, 170, 205, 109, 59, 170, 205, 109, 59, 170, 205
	.byte 109, 59, 170, 205, 109, 59, 170, 205, 109, 59, 170, 205, 109, 59, 170, 205
	.byte 55, 190, 187, 192, 55, 190, 187, 192, 55, 190, 187, 192, 55, 190, 187, 192
	.byte 55, 190, 187, 192, 55, 190, 187, 192, 55, 190, 187, 192, 55, 190, 187, 192
	.byte 55, 190, 187, 192, 55, 190, 187, 192, 55, 190, 187, 192, 55, 190, 187, 192
	.byte 55, 190, 187, 192, 55, 190, 187, 192, 55, 190, 187, 192, 55, 190, 187, 192
	.byte 218, 59, 97, 131, 218, 59, 97, 131, 218, 59, 97, 131, 218, 59, 97, 131
	.byte 218, 59, 97, 131, 218, 59, 97, 131, 218, 59, 97, 131, 218, 59, 97, 131
	.byte 218, 59, 97, 131, 218, 59, 97, 131, 218, 59, 97, 131, 218, 59, 97, 131
	.byte 218, 59, 97, 131, 218, 59, 97, 131, 218, 59, 97, 131, 218, 59, 97, 131
	.byte 99, 163, 72, 219, 99, 163, 72, 219, 99, 163, 72, 219, 99, 163, 72, 219
	.byte 99, 163, 72, 219, 99, 163, 72, 219, 99, 163, 72, 219, 99, 163, 72, 219
	.byte 99, 163, 72, 219, 99, 163, 72, 219, 99, 163, 72, 219, 99, 163, 72, 219
	.byte 99, 163, 72, 219, 99, 163, 72, 219, 99, 163, 72, 219, 99, 163, 72, 219
	.byte 49, 233, 2, 11, 49, 233, 2, 11, 49, 233, 2, 11, 49, 233, 2, 11
	.byte 49, 233, 2, 11, 49, 233, 2, 11, 49, 233, 2, 11, 49, 233, 2, 11
	.byte 49, 233, 2, 11, 49, 233, 2, 11, 49, 233, 2, 11, 49, 233, 2, 11
	.byte 49, 233, 2, 11, 49, 233, 2, 11, 49, 233, 2, 11, 49, 233, 2, 11
	.byte 167, 92, 209, 111, 167, 92, 209, 111, 167, 92, 209, 111, 167, 92, 209, 111
	.byte 167, 92, 209, 111, 167, 92, 209, 111, 167, 92, 209, 111, 167, 92, 209, 111
	.byte 167, 92, 209, 111, 167, 92, 209, 111, 167, 92, 209, 111, 167, 92, 209, 111
	.byte 167, 92, 209, 111, 167, 92, 209, 111, 167, 92, 209, 111, 167, 92, 209, 111
	.byte 202, 250, 26, 82, 202, 250, 26, 82, 202, 250, 26, 82, 202, 250, 26, 82
	.byte 202, 250, 26, 82, 202, 250, 26, 82, 202, 250, 26, 82, 202, 250, 26, 82
	.byte 202, 250, 26, 82, 202, 250, 26, 82, 202, 250, 26, 82, 202, 250, 26, 82
	.byte 202, 250, 26, 82, 202, 250, 26, 82, 202, 250, 26, 82, 202, 250, 26, 82
	.byte 49, 132, 51, 49, 49, 132, 51, 49, 49, 132, 51, 49, 49, 132, 51, 49
	.byte 49, 132, 51, 49, 49, 132, 51, 49, 49, 132, 51, 49, 49, 132, 51, 49
	.byte 49, 132, 51, 49, 49, 132, 51, 49, 49, 132, 51, 49, 49, 132, 51, 49
	.byte 49, 132, 51, 49, 49, 132, 51, 49, 49, 132, 51, 49, 49, 132, 51, 49
	.byte 149, 26, 212, 110, 149, 26, 212, 110, 149, 26, 212, 110, 149, 26, 212, 110
	.byte 149, 26, 212, 110, 149, 26, 212, 110, 149, 26, 212, 110, 149, 26, 212, 110
	.byte 149, 26, 212, 110, 149, 26, 212, 110, 149, 26, 212, 110, 149, 26, 212, 110
	.byte 149, 26, 212, 110, 149, 26, 212, 110, 149, 26, 212, 110, 149, 26, 212, 110
	.byte 144, 120, 67, 109, 144, 120, 67, 109, 144, 120, 67, 109, 144, 120, 67, 109
	.byte 144, 120, 67, 109, 144, 120, 67, 109, 144, 120, 67, 109, 144, 120, 67, 109
	.byte 144, 120, 67, 109, 144, 120, 67, 109, 144, 120, 67, 109, 144, 120, 67, 109
	.byte 144, 120, 67, 109, 144, 120, 67, 109, 144, 120, 67, 109, 144, 120, 67, 109
	.byte 242, 145, 156, 195, 242, 145, 156, 195, 242, 145, 156, 195, 242, 145, 156, 195
	.byte 242, 145, 156, 195, 242, 145, 156, 195, 242, 145, 156, 195, 242, 145, 156, 195
	.byte 242, 145, 156, 195, 242, 145, 156, 195, 242, 145, 156, 195, 242, 145, 156, 195
	.byte 242, 145, 156, 195, 242, 145, 156, 195, 242, 145, 156, 195, 242, 145, 156, 195
	.byte 189, 171, 204, 158, 189, 171, 204, 158, 189, 171, 204, 158, 189, 171, 204, 158
	.byte 189, 171, 204, 158, 189, 171, 204, 158, 189, 171, 204, 158, 189, 171, 204, 158
	.byte 189, 171, 204, 158, 189, 171, 204, 158, 189, 171, 204, 158, 189, 171, 204, 158
	.byte 189, 171, 204, 158, 189, 171, 204, 158, 189, 171, 204, 158, 189, 171, 204, 158
	.byte 230, 160, 201, 181, 230, 160, 201, 181, 230, 160, 201, 181, 230, 160, 201, 181
	.byte 230, 160, 201, 181, 230, 160, 201, 181, 230, 160, 201, 181, 230, 160, 201, 181
	.byte 230, 160, 201, 181, 230, 160, 201, 181, 230, 160, 201, 181, 230, 160, 201, 181
	.byte 230, 160, 201, 181, 230, 160, 201, 181, 230, 160, 201, 181, 230, 160, 201, 181
	.byte 60, 182, 47, 83, 60, 182, 47, 83, 60, 182, 47, 83, 60, 182, 47, 83
	.byte 60, 182, 47, 83, 60, 182, 47, 83, 60, 182, 47, 83, 60, 182, 47, 83
	.byte 60, 182, 47, 83, 60, 182, 47, 83, 60, 182, 47, 83, 60, 182, 47, 83
	.byte 60, 182, 47, 83, 60, 182, 47, 83, 60, 182, 47, 83, 60, 182, 47, 83
	.byte 198, 65, 199, 210, 198, 65, 199, 210, 198, 65, 199, 210, 198, 65, 199, 210
	.byte 198, 65, 199, 210, 198, 65, 199, 210, 198, 65, 199, 210, 198, 65, 199, 210
	.byte 198, 65, 199, 210, 198, 65, 199, 210, 198, 65, 199, 210, 198, 65, 199, 210
	.byte 198, 65, 199, 210, 198, 65, 199, 210, 198, 65, 199, 210, 198, 65, 199, 210
	.byte 163, 126, 35, 7, 163, 126, 35, 7, 163, 126, 35, 7, 163, 126, 35, 7
	.byte 163, 126, 35, 7, 163, 126, 35, 7, 163, 126, 35, 7, 163, 126, 35, 7
	.byte 163, 126, 35, 7, 163, 126, 35, 7, 163, 126, 35, 7, 163, 126, 35, 7
	.byte 163, 126, 35, 7, 163, 126, 35, 7, 163, 126, 35, 7, 163, 126, 35, 7
	.byte 104, 75, 149, 164, 104, 75, 149, 164, 104, 75, 149, 164, 104, 75, 149, 164
	.byte 104, 75, 149, 164, 104, 75, 149, 164, 104, 75, 149, 164, 104, 75, 149, 164
	.byte 104, 75, 149, 164, 104, 75, 149, 164, 104, 75, 149, 164, 104, 75, 149, 164
	.byte 104, 75, 149, 164, 104, 75, 149, 164, 104, 75, 149, 164, 104, 75, 149, 164
	.byte 118, 29, 25, 76, 118, 29, 25, 76, 118, 29, 25, 76, 118, 29, 25, 76
	.byte 118, 29, 25, 76, 118, 29, 25, 76, 118, 29, 25, 76, 118, 29, 25, 76
	.byte 118, 29, 25, 76, 118, 29, 25, 76, 118, 29, 25, 76, 118, 29, 25, 76
	.byte 118, 29, 25, 76, 118, 29, 25, 76, 118, 29, 25, 76, 118, 29, 25, 76
	.byte 103, 230, 9, 106, 103, 230, 9, 106, 103, 230, 9, 106, 103, 230, 9, 106
	.byte 103, 230, 9, 106, 103, 230, 9, 106, 103, 230, 9, 106, 103, 230, 9, 106
	.byte 103, 230, 9, 106, 103, 230, 9, 106, 103, 230, 9, 106, 103, 230, 9, 106
	.byte 103, 230, 9, 106, 103, 230, 9, 106, 103, 230, 9, 106, 103, 230, 9, 106
	.byte 133, 174, 103, 187, 133, 174, 103, 187, 133, 174, 103, 187, 133, 174, 103, 187
	.byte 133, 174, 103, 187, 133, 174, 103, 187, 133, 174, 103, 187, 133, 174, 103, 187
	.byte 133, 174, 103, 187, 133, 174, 103, 187, 133, 174, 103, 187, 133, 174, 103, 187
	.byte 133, 174, 103, 187, 133, 174, 103, 187, 133, 174, 103, 187, 133, 174, 103, 187
	.byte 114, 243, 110, 60, 114, 243, 110, 60, 114, 243, 110, 60, 114, 243, 110, 60
	.byte 114, 243, 110, 60, 114, 243, 110, 60, 114, 243, 110, 60, 114, 243, 110, 60
	.byte 114, 243, 110, 60, 114, 243, 110, 60, 114, 243, 110, 60, 114, 243, 110, 60
	.byte 114, 243, 110, 60, 114, 243, 110, 60, 114, 243, 110, 60, 114, 243, 110, 60
	.byte 58, 245, 79, 165, 58, 245, 79, 165, 58, 245, 79, 165, 58, 245, 79, 165
	.byte 58, 245, 79, 165, 58, 245, 79, 165, 58, 245, 79, 165, 58, 245, 79, 165
	.byte 58, 245, 79, 165, 58, 245, 79, 165, 58, 245, 79, 165, 58, 245, 79, 165
	.byte 58, 245, 79, 165, 58, 245, 79, 165, 58, 245, 79, 165, 58, 245, 79, 165
	.byte 127, 82, 14, 81, 127, 82, 14, 81, 127, 82, 14, 81, 127, 82, 14, 81
	.byte 127, 82, 14, 81, 127, 82, 14, 81, 127, 82, 14, 81, 127, 82, 14, 81
	.byte 127, 82, 14, 81, 127, 82, 14, 81, 127, 82, 14, 81, 127, 82, 14, 81
	.byte 127, 82, 14, 81, 127, 82, 14, 81, 127, 82, 14, 81, 127, 82, 14, 81
	.byte 140, 104, 5, 155, 140, 104, 5, 155, 140, 104, 5, 155, 140, 104, 5, 155
	.byte 140, 104, 5, 155, 140, 104, 5, 155, 140, 104, 5, 155, 140, 104, 5, 155
	.byte 140, 104, 5, 155, 140, 104, 5, 155, 140, 104, 5, 155, 140, 104, 5, 155
	.byte 140, 104, 5, 155, 140, 104, 5, 155, 140, 104, 5, 155, 140, 104, 5, 155
	.byte 171, 217, 131, 31, 171, 217, 131, 31, 171, 217, 131, 31, 171, 217, 131, 31
	.byte 171, 217, 131, 31, 171, 217, 131, 31, 171, 217, 131, 31, 171, 217, 131, 31
	.byte 171, 217, 131, 31, 171, 217, 131, 31, 171, 217, 131, 31, 171, 217, 131, 31
	.byte 171, 217, 131, 31, 171, 217, 131, 31, 171, 217, 131, 31, 171, 217, 131, 31
	.byte 25, 205, 224, 91, 25, 205, 224, 91, 25, 205, 224, 91, 25, 205, 224, 91
	.byte 25, 205, 224, 91, 25, 205, 224, 91, 25, 205, 224, 91, 25, 205, 224, 91
	.byte 25, 205, 224, 91, 25, 205, 224, 91, 25, 205, 224, 91, 25, 205, 224, 91
	.byte 25, 205, 224, 91, 25, 205, 224, 91, 25, 205, 224, 91, 25, 205, 224, 91
	.byte 3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12
	.byte 3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12
	.byte 3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12
	.byte 3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12
	.byte 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0
	.byte 8, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0
	.byte 4, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0
	.byte 12, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0
	.byte 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0
	.byte 10, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0
	.byte 6, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0
	.byte 14, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0
	.byte 0, 0, 0, 0, 2, 0, 0, 0, 16, 0, 0, 0, 18, 0, 0, 0
	.byte 1, 0, 0, 0, 3, 0, 0, 0, 17, 0, 0, 0, 19, 0, 0, 0
	.byte 4, 0, 0, 0, 6, 0, 0, 0, 20, 0, 0, 0, 22, 0, 0, 0
	.byte 5, 0, 0, 0, 7, 0, 0, 0, 21, 0, 0, 0, 23, 0, 0, 0
	.byte 8, 0, 0, 0, 10, 0, 0, 0, 24, 0, 0, 0, 26, 0, 0, 0
	.byte 9, 0, 0, 0, 11, 0, 0, 0, 25, 0, 0, 0, 27, 0, 0, 0
	.byte 12, 0, 0, 0, 14, 0, 0, 0, 28, 0, 0, 0, 30, 0, 0, 0
	.byte 13, 0, 0, 0, 15, 0, 0, 0, 29, 0, 0, 0, 31, 0, 0, 0
	.byte 152, 47, 138, 66, 145, 68, 55, 113, 207, 251, 192, 181, 165, 219, 181, 233
	.byte 91, 194, 86, 57, 241, 17, 241, 89, 164, 130, 63, 146, 213, 94, 28, 171
	.byte 152, 170, 7, 216, 1, 91, 131, 18, 190, 133, 49, 36, 195, 125, 12, 85
	.byte 116, 93, 190, 114, 254, 177, 222, 128, 167, 6, 220, 155, 116, 241, 155, 193
	.byte 193, 105, 155, 228, 134, 71, 190, 239, 198, 157, 193, 15, 204, 161, 12, 36
	.byte 111, 44, 233, 45, 170, 132, 116, 74, 220, 169, 176, 92, 218, 136, 249, 118
	.byte 82, 81, 62, 152, 109, 198, 49, 168, 200, 39, 3, 176, 199, 127, 89, 191
	.byte 243, 11, 224, 198, 71, 145, 167, 213, 81, 99, 202, 6, 103, 41, 41, 20
	.byte 133, 10, 183, 39, 56, 33, 27, 46, 252, 109, 44, 77, 19, 13, 56, 83
	.byte 84, 115, 10, 101, 187, 10, 106, 118, 46, 201, 194, 129, 133, 44, 114, 146
	.byte 161, 232, 191, 162, 75, 102, 26, 168, 112, 139, 75, 194, 163, 81, 108, 199
	.byte 25, 232, 146, 209, 36, 6, 153, 214, 133, 53, 14, 244, 112, 160, 106, 16
	.byte 22, 193, 164, 25, 8, 108, 55, 30, 76, 119, 72, 39, 181, 188, 176, 52
	.byte 179, 12, 28, 57, 74, 170, 216, 78, 79, 202, 156, 91, 243, 111, 46, 104
	.byte 238, 130, 143, 116, 111, 99, 165, 120, 20, 120, 200, 132, 8, 2, 199, 140
	.byte 250, 255, 190, 144, 235, 108, 80, 164, 247, 163, 249, 190, 242, 120, 113, 198
	.byte 152, 47, 138, 194, 145, 68, 55, 113, 207, 251, 192, 181, 165, 219, 181, 233
	.byte 91, 194, 86, 57, 241, 17, 241, 89, 164, 130, 63, 146, 213, 94, 28, 171
	.byte 152, 170, 7, 216, 1, 91, 131, 18, 190, 133, 49, 36, 195, 125, 12, 85
	.byte 116, 93, 190, 114, 254, 177, 222, 128, 167, 6, 220, 155, 116, 243, 155, 193
	.byte 193, 105, 155, 100, 134, 71, 254, 240, 198, 237, 225, 15, 84, 242, 12, 36
	.byte 111, 52, 233, 79, 190, 132, 201, 108, 30, 65, 185, 97, 250, 136, 249, 22
	.byte 82, 81, 198, 242, 109, 90, 142, 168, 101, 252, 25, 176, 199, 158, 217, 185
	.byte 195, 49, 18, 154, 160, 234, 14, 231, 43, 35, 177, 253, 176, 62, 53, 199
	.byte 213, 186, 105, 48, 95, 109, 151, 203, 143, 17, 15, 90, 253, 238, 30, 220
	.byte 137, 182, 53, 10, 4, 122, 11, 222, 157, 202, 244, 88, 22, 91, 93, 225
	.byte 134, 62, 127, 0, 128, 137, 8, 55, 50, 234, 7, 165, 55, 149, 171, 111
	.byte 16, 97, 64, 23, 241, 214, 140, 13, 109, 59, 170, 205, 55, 190, 187, 192
	.byte 218, 59, 97, 131, 99, 163, 72, 219, 49, 233, 2, 11, 167, 92, 209, 111
	.byte 202, 250, 26, 82, 49, 132, 51, 49, 149, 26, 212, 110, 144, 120, 67, 109
	.byte 242, 145, 156, 195, 189, 171, 204, 158, 230, 160, 201, 181, 60, 182, 47, 83
	.byte 198, 65, 199, 210, 163, 126, 35, 7, 104, 75, 149, 164, 118, 29, 25, 76
	.byte 140, 104, 5, 155, 127, 82, 14, 81, 133, 174, 103, 187, 103, 230, 9, 106
	.byte 25, 205, 224, 91, 171, 217, 131, 31, 58, 245, 79, 165, 114, 243, 110, 60
	.byte 3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12
#if defined(__linux__)
	.section .note.GNU-stack,"",@progbits
#endif
#endif
