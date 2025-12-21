/* Control flow primitives for Once
 *
 * C implementation of control.once primitives.
 */

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
/* OnceBuffer is a POINTER to allow storage in intptr_t pairs */
typedef struct { void* data; size_t len; } OnceBufferData;
typedef OnceBufferData* OnceBuffer;
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { intptr_t fst; intptr_t snd; } OncePair;
typedef struct { int tag; intptr_t value; } OnceSum;
#endif

/* ifZero: Branch on zero
 * Returns Left () if zero, Right () if non-zero
 * The sum is allocated on stack and returned by value
 */
OnceSum once_ifZero(int64_t x) {
    OnceSum result;
    if (x == 0) {
        result.tag = 0;  // Left (inl)
        result.value = 0;  // Unit (intptr_t)
    } else {
        result.tag = 1;  // Right (inr)
        result.value = 0;  // Unit (intptr_t)
    }
    return result;
}

/* parseInt: Parse integer from string */
int64_t once_parseInt(OnceString s) {
    if (s.data == NULL || s.len == 0) return 0;
    return (int64_t)atoll(s.data);
}

/* intToString: Convert integer to string */
OnceString once_intToString(int64_t x) {
    // Static buffer for simplicity (not thread-safe, but works for benchmarks)
    static char buf[32];
    int len = snprintf(buf, sizeof(buf), "%ld", (long)x);
    OnceString result = { buf, (size_t)len };
    return result;
}
