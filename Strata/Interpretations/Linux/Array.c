/* Array operations for Once (D042, D044)
 *
 * C implementation of Array.once primitives.
 * Provides indexed read/write access to typed arrays.
 *
 * D044: Array operations are PURE (not effectful).
 * Write operations return the array (same memory) for chaining.
 * QTT determines if mutation is in-place or requires copy.
 *
 * These are the type-specific implementations that the
 * monomorphization pass (D038) dispatches to.
 *
 * D042: Uses element indices, not byte offsets.
 * Array A erases to OnceBuffer at runtime.
 *
 * Invariant: OnceBuffer arguments are always valid (non-null).
 * The type system guarantees this - no runtime checks needed.
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
 * Integer Array Operations (D042, D044: element-indexed, pure)
 *========================================================================*/

/* readInt: Read 64-bit integer at element index */
int64_t once_readInt(OnceBuffer arr, int64_t idx) {
    return ((int64_t*)arr->data)[idx];
}

/* writeInt: Write 64-bit integer at element index (pure, returns array) */
OnceBuffer once_writeInt(OnceBuffer arr, int64_t idx, int64_t value) {
    ((int64_t*)arr->data)[idx] = value;
    return arr;
}

/*========================================================================
 * Float Array Operations (D042, D044: element-indexed, pure)
 *========================================================================*/

/* readFloat: Read 64-bit float (double) at element index */
double once_readFloat(OnceBuffer arr, int64_t idx) {
    return ((double*)arr->data)[idx];
}

/* writeFloat: Write 64-bit float (double) at element index (pure, returns array) */
OnceBuffer once_writeFloat(OnceBuffer arr, int64_t idx, double value) {
    ((double*)arr->data)[idx] = value;
    return arr;
}

/*========================================================================
 * Byte Operations (D044: pure)
 *========================================================================*/

/* readByte: Read single byte at index */
uint8_t once_readByte(OnceBuffer arr, int64_t idx) {
    return ((uint8_t*)arr->data)[idx];
}

/* writeByte: Write single byte at index (pure, returns array) */
OnceBuffer once_writeByte(OnceBuffer arr, int64_t idx, uint8_t value) {
    ((uint8_t*)arr->data)[idx] = value;
    return arr;
}

/*========================================================================
 * Array Length Operations
 *========================================================================*/

/* lengthInt: Get number of Int elements in array */
int64_t once_lengthInt(OnceBuffer arr) {
    return (int64_t)(arr->len / sizeof(int64_t));
}

/* lengthFloat: Get number of Float elements in array */
int64_t once_lengthFloat(OnceBuffer arr) {
    return (int64_t)(arr->len / sizeof(double));
}

/* lengthByte: Get number of Byte elements in array */
int64_t once_lengthByte(OnceBuffer arr) {
    return (int64_t)arr->len;
}

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
