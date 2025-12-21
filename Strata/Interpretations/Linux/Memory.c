/* MallocLike interface implementation for Linux
 * See docs/design/buffers.md for interface specification
 *
 * Allocation failure: crash immediately (abort).
 * Once programs assume allocation succeeds - no Maybe/Option wrapper.
 */

#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
/* OnceBuffer is a POINTER to allow storage in intptr_t pairs */
typedef struct { void* data; size_t len; } OnceBufferData;
typedef OnceBufferData* OnceBuffer;
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { intptr_t fst; intptr_t snd; } OncePair;
typedef struct { int tag; intptr_t value; } OnceSum;
#endif

/* MallocLike interface */

OnceBuffer once_alloc(int64_t size) {
    OnceBuffer buf = (OnceBuffer)malloc(sizeof(OnceBufferData));
    if (!buf) abort();
    buf->data = malloc((size_t)size);
    if (!buf->data) abort();
    buf->len = (size_t)size;
    return buf;
}

void* once_free(OnceBuffer buf) {
    free(buf->data);
    free(buf);
    return ((void*)0);
}

OnceBuffer once_realloc(OnceBuffer buf, int64_t new_size) {
    buf->data = realloc(buf->data, (size_t)new_size);
    if (!buf->data) abort();
    buf->len = (size_t)new_size;
    return buf;
}

/* Typed array allocation (D042)
 * Size is in number of elements, not bytes.
 * Array A erases to OnceBuffer (pointer) at runtime.
 */

/* Allocate array of n Int (64-bit) elements */
OnceBuffer once_allocIntArray(int64_t n) {
    OnceBuffer buf = (OnceBuffer)malloc(sizeof(OnceBufferData));
    if (!buf) abort();
    size_t size = (size_t)n * sizeof(int64_t);
    buf->data = malloc(size);
    if (!buf->data) abort();
    buf->len = size;
    return buf;
}

/* Allocate array of n Float (double) elements */
OnceBuffer once_allocFloatArray(int64_t n) {
    OnceBuffer buf = (OnceBuffer)malloc(sizeof(OnceBufferData));
    if (!buf) abort();
    size_t size = (size_t)n * sizeof(double);
    buf->data = malloc(size);
    if (!buf->data) abort();
    buf->len = size;
    return buf;
}

/* Free typed array (same as free, but for type consistency) */
void* once_freeIntArray(OnceBuffer arr) {
    free(arr->data);
    free(arr);
    return ((void*)0);
}

void* once_freeFloatArray(OnceBuffer arr) {
    free(arr->data);
    free(arr);
    return ((void*)0);
}

/* Helper: allocate and copy string literal to heap
 * Used by @heap annotation in codegen
 * Takes length and source buffer, returns heap-allocated string
 */
OnceString once_heap_string(int64_t len, OnceBuffer src) {
    char* data = (char*)malloc((size_t)len);
    if (!data) abort();
    memcpy(data, src->data, (size_t)len);
    return (OnceString){ .data = data, .len = (size_t)len };
}
