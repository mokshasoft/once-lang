/* MallocLike interface implementation for Linux
 * See docs/design/buffers.md for interface specification
 */

#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
typedef struct { intptr_t fst; intptr_t snd; } OncePair;
typedef struct { int tag; intptr_t value; } OnceSum;
#endif

/* MallocLike interface */

OnceBuffer once_alloc(int64_t size) {
    void* data = malloc((size_t)size);
    return (OnceBuffer){ .data = data, .len = (size_t)size };
}

void* once_free(OnceBuffer buf) {
    free(buf.data);
    return ((void*)0);
}

OnceBuffer once_realloc(OnceBuffer buf, int64_t new_size) {
    void* data = realloc(buf.data, (size_t)new_size);
    return (OnceBuffer){ .data = data, .len = (size_t)new_size };
}

/* Typed array allocation (D042)
 * Size is in number of elements, not bytes.
 * Array A erases to OnceBuffer at runtime.
 */

/* Allocate array of n Int (64-bit) elements */
OnceBuffer once_allocIntArray(int64_t n) {
    size_t size = (size_t)n * sizeof(int64_t);
    void* data = malloc(size);
    return (OnceBuffer){ .data = data, .len = size };
}

/* Allocate array of n Float (double) elements */
OnceBuffer once_allocFloatArray(int64_t n) {
    size_t size = (size_t)n * sizeof(double);
    void* data = malloc(size);
    return (OnceBuffer){ .data = data, .len = size };
}

/* Free typed array (same as free, but for type consistency) */
void* once_freeIntArray(OnceBuffer arr) {
    free(arr.data);
    return ((void*)0);
}

void* once_freeFloatArray(OnceBuffer arr) {
    free(arr.data);
    return ((void*)0);
}

/* Helper: allocate and copy string literal to heap
 * Used by @heap annotation in codegen
 * Takes length and source buffer, returns heap-allocated string
 */
OnceString once_heap_string(int64_t len, OnceBuffer src) {
    char* data = (char*)malloc((size_t)len);
    if (data && src.data) {
        memcpy(data, src.data, (size_t)len);
    }
    return (OnceString){ .data = data, .len = (size_t)len };
}
