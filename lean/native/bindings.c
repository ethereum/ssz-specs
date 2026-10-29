// Bindings between Lean byte arrays and the proved routines printed into kernels_x86.S.
//
// This file only marshals: it turns Lean arrays into pointers, checks that every range lies
// inside its array, and calls a routine. Detection, dispatch and every computation happen in
// the printed routines, which are proved against the model of the processor.
// Where the processor has no hashing kernel, or a range runs past its array, a binding
// calls the Lean body itself.
//
// Clients outside Lean call the printed routines directly, under the SysV calling convention; this file exists
// only for Lean's own compiled code.

#include <lean/lean.h>
#include <stdint.h>

// Test coverage is disabled in ordinary programs. Indices 0..2 count nonempty calls the proved
// dispatchers answered, in PAIRS, COLUMNS, FIXED order; 3..5 count reference fallbacks and
// 6..8 bounds refusals in the same order; 9..10 count general and AVX gathers, 11 gather
// fallbacks and 12 gather refusals. Tests inspect these separately from CPU availability.
enum { COVERAGE_SIZE = 13 };
static uint64_t coverage[COVERAGE_SIZE];
static int coverage_enabled = 0;

static void record_path(unsigned index) {
  if (__atomic_load_n(&coverage_enabled, __ATOMIC_RELAXED))
    __atomic_fetch_add(&coverage[index], 1, __ATOMIC_RELAXED);
}

LEAN_EXPORT lean_obj_res ssz_native_test_begin(void) {
  for (unsigned i = 0; i < COVERAGE_SIZE; ++i) __atomic_store_n(&coverage[i], 0, __ATOMIC_RELAXED);
  __atomic_store_n(&coverage_enabled, 1, __ATOMIC_RELAXED);
  return lean_box(0);
}

LEAN_EXPORT uint64_t ssz_native_test_count(uint32_t index) {
  return index < COVERAGE_SIZE ? __atomic_load_n(&coverage[index], __ATOMIC_RELAXED) : 0;
}

LEAN_EXPORT lean_obj_res ssz_native_test_end(void) {
  __atomic_store_n(&coverage_enabled, 0, __ATOMIC_RELAXED);
  return lean_box(0);
}

// The references, exported from Lean, for processors the kernels cannot run on.
// Each takes ownership of its arrays.
lean_obj_res ssz_native_hash_pairs_reference(lean_obj_arg src, size_t offset, size_t pairs);
lean_obj_res ssz_native_hash_columns_reference(lean_obj_arg left, size_t leftOffset, lean_obj_arg right,
                                             size_t rightOffset, size_t count);
lean_obj_res ssz_native_hash_fixed_reference(lean_obj_arg left, size_t leftOffset, lean_obj_arg node, size_t count);
lean_obj_res ssz_native_gather_reference(lean_obj_arg src, size_t start, size_t stride, size_t width,
                                       size_t count, size_t slot);

#if defined(__x86_64__) && !defined(_WIN32)

// The proved routines: detection, the hashing dispatchers, and the gather dispatcher.
extern const uint8_t ssz_sha256_table[];
extern const uint8_t ssz_zero_roots[];
uint64_t ssz_cpu_features(void);
uint64_t ssz_hash_pairs(uint8_t *out, const uint8_t *left, const uint8_t *right, uint64_t count, const uint64_t *ctx);
uint64_t ssz_hash_columns(uint8_t *out, const uint8_t *left, const uint8_t *right, uint64_t count,
                          const uint64_t *ctx);
uint64_t ssz_hash_fixed(uint8_t *out, const uint8_t *left, const uint8_t *right, uint64_t count, const uint64_t *ctx);
uint64_t ssz_gather_field(uint8_t *out, const uint8_t *src, uint64_t count, const uint64_t *shape,
                          const uint64_t *ctx);

// The detection routine's mask, cut by the tests' restriction, decided on first use.
// Threads racing to decide it all store the same answer, so relaxed atomics suffice.
static uint64_t detected = 0;
enum { DETECTED = 1u << 31 };

static uint64_t mask(void) {
  uint64_t m = __atomic_load_n(&detected, __ATOMIC_RELAXED);
  if (!m) {
    m = ssz_cpu_features() | DETECTED;
    __atomic_store_n(&detected, m, __ATOMIC_RELAXED);
  }
  return m & ~(uint64_t)DETECTED;
}

// The scratch a padded hashing batch needs.
enum { PAD_BYTES = 1536 };

// The context words every routine reads, with a padding area of this call's own.
#define CONTEXT(name)                                                                                \
  uint8_t name##_pad[PAD_BYTES];                                                                     \
  const uint64_t name[4] = {mask(), (uint64_t)ssz_sha256_table, (uint64_t)ssz_zero_roots,           \
                            (uint64_t)name##_pad}

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

// The gather proof interprets even its final, unused source cursor as a natural
// address below 2^63. Check that premise without overflowing the count product.
static int progress_fits(const uint8_t *src, size_t stride, size_t count) {
  uintptr_t address = (uintptr_t)src;
  const uintptr_t bound = UINT64_C(1) << 63;
  return address <= bound && (stride == 0 || count <= (bound - address) / stride);
}

#endif

// BaseIO Unit has no world argument and returns Unit directly in Lean 4.33.
// Keep the hook available on fallback platforms as well as x86-64.
LEAN_EXPORT lean_obj_res ssz_native_restrict(uint32_t mask) {
#if defined(__x86_64__) && !defined(_WIN32)
  __atomic_store_n(&detected, (ssz_cpu_features() & mask) | DETECTED, __ATOMIC_RELAXED);
#else
  (void)mask;
#endif
  return lean_box(0);
}

// BaseIO UInt32 returns the unboxed feature mask, without an IO.Result wrapper.
LEAN_EXPORT uint32_t ssz_native_features(void) {
#if defined(__x86_64__) && !defined(_WIN32)
  return (uint32_t)mask();
#else
  return 0;
#endif
}

#if defined(__x86_64__) && !defined(_WIN32)

// The digests of a run of pairs from one of the proved dispatchers, or nothing when the processor has no kernel.
static lean_object *dispatched(uint64_t (*routine)(uint8_t *, const uint8_t *, const uint8_t *, uint64_t,
                                                   const uint64_t *),
                               const uint8_t *left, const uint8_t *right, size_t count) {
  lean_object *out = alloc_bytes(32 * count);
  CONTEXT(ctx);
  if (routine(lean_sarray_cptr(out), left, right, count, ctx) == 0) return out;
  lean_dec(out);
  return NULL;
}

#endif

LEAN_EXPORT lean_obj_res ssz_native_hash_pairs(b_lean_obj_arg src, size_t offset, size_t pairs) {
#if defined(__x86_64__) && !defined(_WIN32)
  // The routines need every input byte present; anything else takes the reference's reading of it.
  if (fits(src, offset, 64, pairs) && fits(src, offset + 32, 64, pairs)) {
    const uint8_t *in = lean_sarray_cptr(src) + offset;
    lean_object *out = dispatched(ssz_hash_pairs, in, in + 32, pairs);
    if (out) {
      if (pairs) record_path(0);
      return out;
    }
  } else record_path(6);
#endif
  // The caller keeps its borrowed array, so the reference gets a reference of its own.
  lean_inc(src);
  record_path(3);
  return ssz_native_hash_pairs_reference(src, offset, pairs);
}

LEAN_EXPORT lean_obj_res ssz_native_hash_columns(b_lean_obj_arg left, size_t leftOffset, b_lean_obj_arg right,
                                               size_t rightOffset, size_t count) {
#if defined(__x86_64__) && !defined(_WIN32)
  if (fits(left, leftOffset, 32, count) && fits(right, rightOffset, 32, count)) {
    lean_object *out = dispatched(ssz_hash_columns, lean_sarray_cptr(left) + leftOffset,
                                  lean_sarray_cptr(right) + rightOffset, count);
    if (out) {
      if (count) record_path(1);
      return out;
    }
  } else record_path(7);
#endif
  lean_inc(left);
  lean_inc(right);
  record_path(4);
  return ssz_native_hash_columns_reference(left, leftOffset, right, rightOffset, count);
}

LEAN_EXPORT lean_obj_res ssz_native_hash_fixed(b_lean_obj_arg left, size_t leftOffset, b_lean_obj_arg node,
                                             size_t count) {
#if defined(__x86_64__) && !defined(_WIN32)
  if (fits(left, leftOffset, 32, count) && lean_sarray_size(node) >= 32) {
    lean_object *out = dispatched(ssz_hash_fixed, lean_sarray_cptr(left) + leftOffset, lean_sarray_cptr(node), count);
    if (out) {
      if (count) record_path(2);
      return out;
    }
  } else record_path(8);
#endif
  lean_inc(left);
  lean_inc(node);
  record_path(5);
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
  if (inside && progress_fits(lean_sarray_cptr(src) + start, stride, count) &&
      (count == 0 || slot <= (SIZE_MAX / 2) / count)) {
    lean_object *out = alloc_bytes(slot * count);
    const uint64_t shape[3] = {width, stride - width, slot - width};
    CONTEXT(ctx);
    uint64_t path = ssz_gather_field(lean_sarray_cptr(out), lean_sarray_cptr(src) + start, count, shape, ctx);
    if (count) record_path(path ? 10 : 9);
    return out;
  }
  record_path(12);
#endif
  lean_inc(src);
  record_path(11);
  return ssz_native_gather_reference(src, start, stride, width, count, slot);
}
