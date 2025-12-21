/* Integer arithmetic primitives for Once
 *
 * C implementation of arith.once primitives.
 * These are pure functions (no side effects).
 */

#include <stdint.h>
#include <stdlib.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
typedef struct { intptr_t fst; intptr_t snd; } OncePair;
typedef struct { int tag; intptr_t value; } OnceSum;
#endif

/*========================================================================
 * Basic Arithmetic
 *========================================================================*/

int64_t once_add(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a + b;
}

int64_t once_sub(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a - b;
}

int64_t once_mul(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a * b;
}

int64_t once_div(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    if (b == 0) return 0;  // Avoid division by zero
    return a / b;
}

int64_t once_mod(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    if (b == 0) return 0;  // Avoid division by zero
    return a % b;
}

int64_t once_neg(int64_t x) {
    return -x;
}

int64_t once_abs(int64_t x) {
    return x < 0 ? -x : x;
}

/*========================================================================
 * Comparisons (return 0 or 1)
 *========================================================================*/

int64_t once_eq(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a == b ? 1 : 0;
}

int64_t once_neq(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a != b ? 1 : 0;
}

int64_t once_lt(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a < b ? 1 : 0;
}

int64_t once_le(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a <= b ? 1 : 0;
}

int64_t once_gt(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a > b ? 1 : 0;
}

int64_t once_ge(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a >= b ? 1 : 0;
}

/*========================================================================
 * Bitwise Operations
 *========================================================================*/

int64_t once_band(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a & b;
}

int64_t once_bor(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a | b;
}

int64_t once_bxor(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a ^ b;
}

int64_t once_bnot(int64_t x) {
    return ~x;
}

int64_t once_shl(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a << b;
}

int64_t once_shr(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a >> b;
}

/*========================================================================
 * Min/Max
 *========================================================================*/

int64_t once_min(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a < b ? a : b;
}

int64_t once_max(OncePair p) {
    int64_t a = (int64_t)p.fst;
    int64_t b = (int64_t)p.snd;
    return a > b ? a : b;
}
