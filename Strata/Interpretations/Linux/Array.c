/* Array operations for Once
 *
 * C implementation of Array.once primitives.
 * Provides indexed read/write access to buffers.
 *
 * These are the type-specific implementations that the
 * monomorphization pass (D038) dispatches to.
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
 * Integer Array Operations
 *========================================================================*/

/* readInt: Read 64-bit integer at byte offset */
int64_t once_readInt(OnceBuffer buf, int64_t offset) {
    if (buf.data == NULL) return 0;
    if (offset < 0 || (size_t)(offset + 8) > buf.len) return 0;

    int64_t value;
    memcpy(&value, (char*)buf.data + offset, sizeof(int64_t));
    return value;
}

/* writeInt: Write 64-bit integer at byte offset */
void* once_writeInt(OnceBuffer buf, int64_t offset, int64_t value) {
    if (buf.data != NULL &&
        offset >= 0 && (size_t)(offset + 8) <= buf.len) {
        memcpy((char*)buf.data + offset, &value, sizeof(int64_t));
    }
    return (void*)0;
}

/*========================================================================
 * Float Array Operations
 *========================================================================*/

/* readFloat: Read 64-bit float (double) at byte offset */
double once_readFloat(OnceBuffer buf, int64_t offset) {
    if (buf.data == NULL) return 0.0;
    if (offset < 0 || (size_t)(offset + 8) > buf.len) return 0.0;

    double value;
    memcpy(&value, (char*)buf.data + offset, sizeof(double));
    return value;
}

/* writeFloat: Write 64-bit float (double) at byte offset */
void* once_writeFloat(OnceBuffer buf, int64_t offset, double value) {
    if (buf.data != NULL &&
        offset >= 0 && (size_t)(offset + 8) <= buf.len) {
        memcpy((char*)buf.data + offset, &value, sizeof(double));
    }
    return (void*)0;
}

/*========================================================================
 * Byte Operations
 *========================================================================*/

/* readByte: Read single byte at offset */
uint8_t once_readByte(OnceBuffer buf, int64_t offset) {
    if (buf.data == NULL) return 0;
    if (offset < 0 || (size_t)offset >= buf.len) return 0;

    return ((uint8_t*)buf.data)[offset];
}

/* writeByte: Write single byte at offset */
void* once_writeByte(OnceBuffer buf, int64_t offset, uint8_t value) {
    if (buf.data != NULL &&
        offset >= 0 && (size_t)offset < buf.len) {
        ((uint8_t*)buf.data)[offset] = value;
    }
    return (void*)0;
}

/*========================================================================
 * Bulk Operations
 *========================================================================*/

/* memcpy: Copy bytes between buffers */
void* once_memcpy(OnceBuffer dest, int64_t destOff,
                  OnceBuffer src, int64_t srcOff, int64_t count) {
    if (dest.data != NULL && src.data != NULL &&
        destOff >= 0 && srcOff >= 0 && count > 0 &&
        (size_t)(destOff + count) <= dest.len &&
        (size_t)(srcOff + count) <= src.len) {
        memmove((char*)dest.data + destOff,
                (char*)src.data + srcOff,
                (size_t)count);
    }
    return (void*)0;
}

/* memset: Fill buffer with byte value */
void* once_memset(OnceBuffer buf, int64_t offset, int64_t value, int64_t count) {
    if (buf.data != NULL &&
        offset >= 0 && count > 0 &&
        (size_t)(offset + count) <= buf.len) {
        memset((char*)buf.data + offset, (int)value, (size_t)count);
    }
    return (void*)0;
}
