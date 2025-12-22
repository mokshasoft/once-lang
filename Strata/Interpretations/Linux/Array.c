/* Array operations for Once (D042, D044, D046)
 *
 * C implementation of Array.once primitives.
 *
 * D046: Generic array operations (read, write, length) are now generated
 * inline by the compiler based on element type. No type-specific C functions
 * are needed - the compiler extracts the element type from TArray and
 * generates the appropriate C code directly.
 *
 * This file only contains:
 * - Type definitions (OnceBuffer, etc.)
 * - Bulk operations (memcpy, memset) that work on raw bytes
 */

#include <stdint.h>
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

/*========================================================================
 * Bulk Operations (D044: pure, return updated arrays)
 *========================================================================*/

/* memcpy: Copy bytes between arrays (pure, returns destination) */
OnceBuffer once_memcpy(OnceBuffer dest, int64_t destOff,
                       OnceBuffer src, int64_t srcOff, int64_t count) {
    memmove((char*)dest->data + destOff,
            (char*)src->data + srcOff,
            (size_t)count);
    return dest;
}

/* memset: Fill array region with byte value (pure, returns array) */
OnceBuffer once_memset(OnceBuffer arr, int64_t offset, int64_t value, int64_t count) {
    memset((char*)arr->data + offset, (int)value, (size_t)count);
    return arr;
}
