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
 */

#include <stdint.h>
#include <string.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
typedef struct { intptr_t fst; intptr_t snd; } OncePair;
typedef struct { int tag; intptr_t value; } OnceSum;
#endif

/*========================================================================
 * Integer Array Operations (D042, D044: element-indexed, pure)
 *========================================================================*/

/* readInt: Read 64-bit integer at element index */
int64_t once_readInt(OnceBuffer arr, int64_t idx) {
    if (arr.data == NULL) return 0;
    size_t byte_offset = (size_t)idx * sizeof(int64_t);
    if (idx < 0 || byte_offset + sizeof(int64_t) > arr.len) return 0;

    return ((int64_t*)arr.data)[idx];
}

/* writeInt: Write 64-bit integer at element index (pure, returns array) */
OnceBuffer once_writeInt(OnceBuffer arr, int64_t idx, int64_t value) {
    if (arr.data != NULL && idx >= 0) {
        size_t byte_offset = (size_t)idx * sizeof(int64_t);
        if (byte_offset + sizeof(int64_t) <= arr.len) {
            ((int64_t*)arr.data)[idx] = value;
        }
    }
    return arr;  /* Return same array for chaining */
}

/*========================================================================
 * Float Array Operations (D042, D044: element-indexed, pure)
 *========================================================================*/

/* readFloat: Read 64-bit float (double) at element index */
double once_readFloat(OnceBuffer arr, int64_t idx) {
    if (arr.data == NULL) return 0.0;
    size_t byte_offset = (size_t)idx * sizeof(double);
    if (idx < 0 || byte_offset + sizeof(double) > arr.len) return 0.0;

    return ((double*)arr.data)[idx];
}

/* writeFloat: Write 64-bit float (double) at element index (pure, returns array) */
OnceBuffer once_writeFloat(OnceBuffer arr, int64_t idx, double value) {
    if (arr.data != NULL && idx >= 0) {
        size_t byte_offset = (size_t)idx * sizeof(double);
        if (byte_offset + sizeof(double) <= arr.len) {
            ((double*)arr.data)[idx] = value;
        }
    }
    return arr;  /* Return same array for chaining */
}

/*========================================================================
 * Byte Operations (D044: pure)
 *========================================================================*/

/* readByte: Read single byte at index */
uint8_t once_readByte(OnceBuffer arr, int64_t idx) {
    if (arr.data == NULL) return 0;
    if (idx < 0 || (size_t)idx >= arr.len) return 0;

    return ((uint8_t*)arr.data)[idx];
}

/* writeByte: Write single byte at index (pure, returns array) */
OnceBuffer once_writeByte(OnceBuffer arr, int64_t idx, uint8_t value) {
    if (arr.data != NULL && idx >= 0 && (size_t)idx < arr.len) {
        ((uint8_t*)arr.data)[idx] = value;
    }
    return arr;  /* Return same array for chaining */
}

/*========================================================================
 * Array Length Operations
 *========================================================================*/

/* lengthInt: Get number of Int elements in array */
int64_t once_lengthInt(OnceBuffer arr) {
    if (arr.data == NULL) return 0;
    return (int64_t)(arr.len / sizeof(int64_t));
}

/* lengthFloat: Get number of Float elements in array */
int64_t once_lengthFloat(OnceBuffer arr) {
    if (arr.data == NULL) return 0;
    return (int64_t)(arr.len / sizeof(double));
}

/* lengthByte: Get number of Byte elements in array */
int64_t once_lengthByte(OnceBuffer arr) {
    if (arr.data == NULL) return 0;
    return (int64_t)arr.len;
}

/*========================================================================
 * Bulk Operations (D044: pure, return updated arrays)
 *========================================================================*/

/* memcpy: Copy bytes between arrays (pure, returns destination) */
OnceBuffer once_memcpy(OnceBuffer dest, int64_t destOff,
                       OnceBuffer src, int64_t srcOff, int64_t count) {
    if (dest.data != NULL && src.data != NULL &&
        destOff >= 0 && srcOff >= 0 && count > 0 &&
        (size_t)(destOff + count) <= dest.len &&
        (size_t)(srcOff + count) <= src.len) {
        memmove((char*)dest.data + destOff,
                (char*)src.data + srcOff,
                (size_t)count);
    }
    return dest;  /* Return destination array for chaining */
}

/* memset: Fill array region with byte value (pure, returns array) */
OnceBuffer once_memset(OnceBuffer arr, int64_t offset, int64_t value, int64_t count) {
    if (arr.data != NULL &&
        offset >= 0 && count > 0 &&
        (size_t)(offset + count) <= arr.len) {
        memset((char*)arr.data + offset, (int)value, (size_t)count);
    }
    return arr;  /* Return array for chaining */
}
