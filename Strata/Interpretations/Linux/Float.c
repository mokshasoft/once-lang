/* Floating-point arithmetic primitives for Once
 *
 * C implementation of Float.once primitives.
 * Uses double-precision (64-bit) floating point.
 */

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
typedef struct { void* fst; void* snd; } OncePair;
typedef struct { int tag; void* value; } OnceSum;
#endif

/* Helper to extract doubles from OncePair
 * Float values are passed as double, stored in void* via type punning
 */
static inline double pair_fst_double(OncePair p) {
    double d;
    memcpy(&d, &p.fst, sizeof(double));
    return d;
}

static inline double pair_snd_double(OncePair p) {
    double d;
    memcpy(&d, &p.snd, sizeof(double));
    return d;
}

static inline double int64_to_double_bits(int64_t x) {
    double d;
    memcpy(&d, &x, sizeof(double));
    return d;
}

static inline int64_t double_to_int64_bits(double d) {
    int64_t x;
    memcpy(&x, &d, sizeof(int64_t));
    return x;
}

/*========================================================================
 * Basic Arithmetic
 *========================================================================*/

double once_fadd(OncePair p) {
    return pair_fst_double(p) + pair_snd_double(p);
}

double once_fsub(OncePair p) {
    return pair_fst_double(p) - pair_snd_double(p);
}

double once_fmul(OncePair p) {
    return pair_fst_double(p) * pair_snd_double(p);
}

double once_fdiv(OncePair p) {
    return pair_fst_double(p) / pair_snd_double(p);
}

double once_fneg(double x) {
    return -x;
}

double once_fabs(double x) {
    return fabs(x);
}

/*========================================================================
 * Transcendental Functions
 *========================================================================*/

double once_fsqrt(double x) {
    return sqrt(x);
}

double once_fsin(double x) {
    return sin(x);
}

double once_fcos(double x) {
    return cos(x);
}

double once_fpow(OncePair p) {
    return pow(pair_fst_double(p), pair_snd_double(p));
}

double once_flog(double x) {
    return log(x);
}

double once_fexp(double x) {
    return exp(x);
}

/*========================================================================
 * Comparisons (return 0 or 1)
 *========================================================================*/

int64_t once_flt(OncePair p) {
    return pair_fst_double(p) < pair_snd_double(p) ? 1 : 0;
}

int64_t once_fle(OncePair p) {
    return pair_fst_double(p) <= pair_snd_double(p) ? 1 : 0;
}

int64_t once_fgt(OncePair p) {
    return pair_fst_double(p) > pair_snd_double(p) ? 1 : 0;
}

int64_t once_fge(OncePair p) {
    return pair_fst_double(p) >= pair_snd_double(p) ? 1 : 0;
}

int64_t once_feq(OncePair p) {
    return pair_fst_double(p) == pair_snd_double(p) ? 1 : 0;
}

int64_t once_fne(OncePair p) {
    return pair_fst_double(p) != pair_snd_double(p) ? 1 : 0;
}

/*========================================================================
 * Conversions
 *========================================================================*/

double once_intToFloat(int64_t x) {
    return (double)x;
}

int64_t once_floatToInt(double x) {
    return (int64_t)x;
}

double once_parseFloat(OnceString s) {
    if (s.data == NULL || s.len == 0) return 0.0;
    return atof(s.data);
}

OnceString once_floatToString(double x) {
    /* Static buffer for simplicity (not thread-safe) */
    static char buf[64];
    int len = snprintf(buf, sizeof(buf), "%.17g", x);
    OnceString result = { buf, (size_t)len };
    return result;
}

/*========================================================================
 * Constants
 *========================================================================*/

double once_pi(void* x) {
    (void)x;
    return 3.14159265358979323846;
}

/*========================================================================
 * Min/Max
 *========================================================================*/

double once_fmin(OncePair p) {
    double a = pair_fst_double(p);
    double b = pair_snd_double(p);
    return a < b ? a : b;
}

double once_fmax(OncePair p) {
    double a = pair_fst_double(p);
    double b = pair_snd_double(p);
    return a > b ? a : b;
}
