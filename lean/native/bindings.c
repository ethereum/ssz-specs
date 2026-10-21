// Bindings between Lean byte arrays and the kernels printed into kernels_x86.S.
//
// Each binding computes exactly what its Lean definition's body computes.
// The kernels are proved to compute those bodies on a model of the processor.
// Every call meets the proofs' hypotheses: the output is a fresh array, apart from the inputs and the table.
// Where the processor lacks the kernels' instructions, a binding calls the Lean body itself.

#include <lean/lean.h>
#include <stdint.h>

// The references, exported from Lean, for processors the kernels cannot run on.
// Each takes ownership of its arrays.
lean_obj_res ssz_native_hash_pairs_reference(lean_obj_arg src, size_t offset, size_t pairs);
lean_obj_res ssz_native_hash_columns_reference(lean_obj_arg left, size_t leftOffset, lean_obj_arg right,
                                             size_t rightOffset, size_t count);
lean_obj_res ssz_native_hash_fixed_reference(lean_obj_arg left, size_t leftOffset, lean_obj_arg node, size_t count);
lean_obj_res ssz_native_gather_reference(lean_obj_arg src, size_t start, size_t stride, size_t width,
                                       size_t count, size_t slot);

#if defined(__x86_64__) && !defined(_WIN32)

extern const uint8_t ssz_sha256_table[];
void ssz_sha256_avx512_pairs(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t batches,
                           const uint8_t *table);
void ssz_sha256_avx512_columns(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t batches,
                             const uint8_t *table);
void ssz_sha256_shani_pairs(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t pairs,
                             const uint8_t *table);
void ssz_sha256_shani_columns(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t pairs,
                               const uint8_t *table);
void ssz_sha256_avx512_fixed(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t batches,
                           const uint8_t *table);
void ssz_sha256_shani_fixed(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t pairs,
                             const uint8_t *table);
void ssz_sha256_shani_dual_pairs(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t twos,
                                 const uint8_t *table);
void ssz_sha256_shani_dual_columns(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t twos,
                                   const uint8_t *table);
void ssz_sha256_shani_dual_fixed(uint8_t *out, const uint8_t *left, const uint8_t *right, size_t twos,
                                 const uint8_t *table);
void ssz_gather(uint8_t *out, const uint8_t *src, size_t count, size_t width, size_t skip, size_t pad);
void ssz_gather_1(uint8_t *out, const uint8_t *src, size_t count, size_t width, size_t skip, size_t pad);
void ssz_gather_2(uint8_t *out, const uint8_t *src, size_t count, size_t width, size_t skip, size_t pad);
void ssz_gather_4(uint8_t *out, const uint8_t *src, size_t count, size_t width, size_t skip, size_t pad);
void ssz_gather_8(uint8_t *out, const uint8_t *src, size_t count, size_t width, size_t skip, size_t pad);
void ssz_gather_16(uint8_t *out, const uint8_t *src, size_t count, size_t width, size_t skip, size_t pad);
void ssz_gather_32(uint8_t *out, const uint8_t *src, size_t count, size_t width, size_t skip, size_t pad);
void ssz_gather_key(uint8_t *out, const uint8_t *src, size_t count, size_t width, size_t skip, size_t pad);

// What this processor and its operating system support, one bit each.
enum { NARROW = 1, WIDE = 2, AVX = 4, DETECTED = 8 };

// The answer, decided on first use.
// Threads racing to decide it all store the same answer, so relaxed atomics suffice.
static int detected = 0;

static void cpuid(uint32_t leaf, uint32_t sub, uint32_t r[4]) {
  // Leaf and subleaf in, the four result registers out.
  __asm__ volatile("cpuid" : "=a"(r[0]), "=b"(r[1]), "=c"(r[2]), "=d"(r[3]) : "a"(leaf), "c"(sub));
}

static int detect(void) {
  uint32_t r[4];
  cpuid(0, 0, r);
  if (r[0] < 7) return DETECTED;
  cpuid(1, 0, r);
  // The operating system must save the vector state, or the wider registers are unusable.
  int osxsave = (r[2] >> 27) & 1;
  int ssse3 = (r[2] >> 9) & 1;
  int sse41 = (r[2] >> 19) & 1;
  int avx = (r[2] >> 28) & 1;
  uint64_t xcr0 = 0;
  if (osxsave) {
    uint32_t lo, hi;
    __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
    xcr0 = ((uint64_t)hi << 32) | lo;
  }
  cpuid(7, 0, r);
  int sha = (r[1] >> 29) & 1;
  // AVX-512 foundation, byte and word operations, and the 256-bit forms.
  int avx512 = ((r[1] >> 16) & 1) && ((r[1] >> 30) & 1) && ((r[1] >> 31) & 1);
  // The saved state covers SSE and AVX, then the opmasks and both parts of the upper zmm registers.
  int ymmState = (xcr0 & 0x6) == 0x6;
  int zmmState = (xcr0 & 0xE6) == 0xE6;
  return DETECTED | (sha && ssse3 && sse41 ? NARROW : 0) | (avx512 && avx && zmmState ? WIDE : 0) |
         (avx && ymmState ? AVX : 0);
}

static int kernels(void) {
  int k = __atomic_load_n(&detected, __ATOMIC_RELAXED);
  if (!k) {
    k = detect();
    __atomic_store_n(&detected, k, __ATOMIC_RELAXED);
  }
  return k;
}

// Restricts the kernels to those whose bits a mask keeps, so tests can run each path on one processor.
LEAN_EXPORT lean_obj_res ssz_native_restrict(uint32_t mask, lean_obj_arg world) {
  (void)world;
  __atomic_store_n(&detected, (detect() & (int)mask) | DETECTED, __ATOMIC_RELAXED);
  return lean_io_result_mk_ok(lean_box(0));
}

// The three layouts the kernels come in, by the strides of their left and right nodes.
enum layout { PAIRS, COLUMNS, FIXED };

// Parent i hashes the node at left + ls * i followed by the node at right + rs * i.
static void hash(int k, enum layout layout, uint8_t *out, const uint8_t *left, const uint8_t *right,
                 size_t count) {
  size_t ls = layout == PAIRS ? 64 : 32;
  size_t rs = layout == PAIRS ? 64 : layout == COLUMNS ? 32 : 0;
  // Whole batches of sixteen go to the AVX-512 kernel when there is one.
  if (k & WIDE) {
    size_t batches = count / 16;
    if (layout == PAIRS) ssz_sha256_avx512_pairs(out, left, right, batches, ssz_sha256_table);
    else if (layout == COLUMNS) ssz_sha256_avx512_columns(out, left, right, batches, ssz_sha256_table);
    else ssz_sha256_avx512_fixed(out, left, right, batches, ssz_sha256_table);
    out += 512 * batches;
    left += 16 * ls * batches;
    right += 16 * rs * batches;
    count -= 16 * batches;
    if (count == 0) return;
    // Without the SHA-NI kernel, a short tail runs as one batch padded with zeros.
    if (!(k & NARROW)) {
      uint8_t batch[1024] = {0};
      uint8_t digests[512];
      for (size_t i = 0; i < count; i++) {
        __builtin_memcpy(batch + 64 * i, left + ls * i, 32);
        __builtin_memcpy(batch + 64 * i + 32, right + rs * i, 32);
      }
      ssz_sha256_avx512_pairs(digests, batch, batch + 32, 1, ssz_sha256_table);
      __builtin_memcpy(out, digests, 32 * count);
      return;
    }
  }
  // Pairs go two at a time to the interleaved kernel, and a last odd one alone.
  size_t twos = count / 2;
  if (twos) {
    if (layout == PAIRS) ssz_sha256_shani_dual_pairs(out, left, right, twos, ssz_sha256_table);
    else if (layout == COLUMNS) ssz_sha256_shani_dual_columns(out, left, right, twos, ssz_sha256_table);
    else ssz_sha256_shani_dual_fixed(out, left, right, twos, ssz_sha256_table);
    out += 64 * twos;
    left += 2 * ls * twos;
    right += 2 * rs * twos;
    count -= 2 * twos;
    if (count == 0) return;
  }
  if (layout == PAIRS) ssz_sha256_shani_pairs(out, left, right, count, ssz_sha256_table);
  else if (layout == COLUMNS) ssz_sha256_shani_columns(out, left, right, count, ssz_sha256_table);
  else ssz_sha256_shani_fixed(out, left, right, count, ssz_sha256_table);
}

// A byte array of a size, with room for one more node.
// An odd tree level grows by one node, which then needs no copy.
// The size must leave room for that node below the largest size an object can have.
static lean_object *alloc_bytes(size_t size) {
  return lean_alloc_sarray(1, size, size + 32);
}

// Whether n nodes of 32 bytes, a stride apart, fit in an array from a byte offset.
static int fits(b_lean_obj_arg a, size_t offset, size_t stride, size_t n) {
  size_t size = lean_sarray_size(a);
  if (n == 0) return offset <= size;
  return size >= 32 && n - 1 <= (size - 32) / stride && offset <= size - 32 - stride * (n - 1);
}

#endif

LEAN_EXPORT lean_obj_res ssz_native_hash_pairs(b_lean_obj_arg src, size_t offset, size_t pairs) {
#if defined(__x86_64__) && !defined(_WIN32)
  int k = kernels();
  // The kernels need every input byte present.
  // Anything else takes the reference's reading of it.
  if ((k & (NARROW | WIDE)) && fits(src, offset, 64, pairs) && fits(src, offset + 32, 64, pairs)) {
    lean_object *out = alloc_bytes(32 * pairs);
    const uint8_t *in = lean_sarray_cptr(src) + offset;
    hash(k, PAIRS, lean_sarray_cptr(out), in, in + 32, pairs);
    return out;
  }
#endif
  // The caller keeps its borrowed array, so the reference gets a reference of its own.
  lean_inc(src);
  return ssz_native_hash_pairs_reference(src, offset, pairs);
}

LEAN_EXPORT lean_obj_res ssz_native_hash_columns(b_lean_obj_arg left, size_t leftOffset, b_lean_obj_arg right,
                                               size_t rightOffset, size_t count) {
#if defined(__x86_64__) && !defined(_WIN32)
  int k = kernels();
  if ((k & (NARROW | WIDE)) && fits(left, leftOffset, 32, count) && fits(right, rightOffset, 32, count)) {
    lean_object *out = alloc_bytes(32 * count);
    hash(k, COLUMNS, lean_sarray_cptr(out), lean_sarray_cptr(left) + leftOffset,
         lean_sarray_cptr(right) + rightOffset, count);
    return out;
  }
#endif
  lean_inc(left);
  lean_inc(right);
  return ssz_native_hash_columns_reference(left, leftOffset, right, rightOffset, count);
}

LEAN_EXPORT lean_obj_res ssz_native_hash_fixed(b_lean_obj_arg left, size_t leftOffset, b_lean_obj_arg node,
                                             size_t count) {
#if defined(__x86_64__) && !defined(_WIN32)
  int k = kernels();
  if ((k & (NARROW | WIDE)) && fits(left, leftOffset, 32, count) && lean_sarray_size(node) >= 32) {
    lean_object *out = alloc_bytes(32 * count);
    hash(k, FIXED, lean_sarray_cptr(out), lean_sarray_cptr(left) + leftOffset, lean_sarray_cptr(node), count);
    return out;
  }
#endif
  lean_inc(left);
  lean_inc(node);
  return ssz_native_hash_fixed_reference(left, leftOffset, node, count);
}

LEAN_EXPORT lean_obj_res ssz_native_gather(b_lean_obj_arg src, size_t start, size_t stride, size_t width,
                                         size_t count, size_t slot) {
#if defined(__x86_64__) && !defined(_WIN32)
  size_t size = lean_sarray_size(src);
  // Every field must lie inside the source, and fit its slot.
  // A zero stride is accepted only for empty fields, which gives a buffer of zeros.
  int inside = width <= slot && start <= size && (stride == 0 ? width == 0 : width <= stride) &&
               (count == 0 || stride == 0 ||
                (count - 1 <= (size - start) / stride && width <= size - start - stride * (count - 1)));
  // The output, with its spare node, must have a size the allocator can represent.
  if (inside && (count == 0 || slot <= (SIZE_MAX / 2) / count)) {
    lean_object *out = alloc_bytes(slot * count);
    uint8_t *o = lean_sarray_cptr(out);
    const uint8_t *in = lean_sarray_cptr(src) + start;
    size_t skip = stride - width, pad = slot - width;
    // The common widths each have a routine with one load and one store per field.
    void (*routine)(uint8_t *, const uint8_t *, size_t, size_t, size_t, size_t) = ssz_gather;
    if ((kernels() & AVX) && slot == 32) {
      if (width == 1) routine = ssz_gather_1;
      else if (width == 2) routine = ssz_gather_2;
      else if (width == 4) routine = ssz_gather_4;
      else if (width == 8) routine = ssz_gather_8;
      else if (width == 16) routine = ssz_gather_16;
      else if (width == 32) routine = ssz_gather_32;
    } else if ((kernels() & AVX) && slot == 64 && width == 48) {
      routine = ssz_gather_key;
    }
    routine(o, in, count, width, skip, pad);
    return out;
  }
#endif
  lean_inc(src);
  return ssz_native_gather_reference(src, start, stride, width, count, slot);
}
