/* Array operations for Once (D040)
 *
 * C implementation of Array.once primitives.
 *
 * Generic array operations (read, write, length) will be generated inline
 * by the compiler based on element type. For now, they can be implemented
 * in interpretation files per element type.
 *
 * This file contains:
 * - Type definitions (OnceBuffer, etc.)
 * - Bulk operations (memcpy, memset) that work on raw bytes
 */

#include <stdint.h>
#include <string.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
typedef struct { void* fst; void* snd; } OncePair;
typedef struct { int tag; void* value; } OnceSum;
#endif

/*========================================================================
 * Bulk Operations (pure, return updated arrays)
 *========================================================================*/

/* memcpy: Copy bytes between arrays (pure, returns destination) */
OnceBuffer once_memcpy(OnceBuffer dest, int64_t destOff,
                       OnceBuffer src, int64_t srcOff, int64_t count) {
    memmove((char*)dest.data + destOff,
            (char*)src.data + srcOff,
            (size_t)count);
    return dest;
}

/* memset: Fill array region with byte value (pure, returns array) */
OnceBuffer once_memset(OnceBuffer arr, int64_t offset, int64_t value, int64_t count) {
    memset((char*)arr.data + offset, (int)value, (size_t)count);
    return arr;
}
