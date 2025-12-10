/* MallocLike interface implementation for Linux
 * See docs/design/buffers.md for interface specification
 */

#include <stdlib.h>
#include <string.h>

/* OnceBuffer type */
typedef struct {
    void* data;
    size_t len;
} OnceBuffer;

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
