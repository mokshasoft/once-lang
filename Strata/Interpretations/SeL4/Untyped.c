/* seL4 Untyped Memory Primitives - C Backend Stubs
 *
 * These are stub implementations for the C backend.
 * For actual seL4 usage, use the architecture-specific assembly implementations.
 */

#include <stdint.h>
#include <stddef.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
#endif

/* Pair type for tuple passing */
#ifndef ONCE_PAIR_DEFINED
#define ONCE_PAIR_DEFINED
typedef struct { void* fst; void* snd; } OncePair;
#endif

/* seL4_Untyped_Retype stub
 *
 * Arguments (as nested pairs):
 *   untyped, objectType, sizeBits, root, nodeIndex, nodeDepth, nodeOffset, numObjects
 *
 * Returns: 0 (success)
 */
void* once_seL4_Untyped_Retype(OncePair args) {
    /* In real seL4, this would invoke the Untyped capability
     * to create new kernel objects.
     *
     * For stub purposes, we just return success (0).
     */
    (void)args;
    return (void*)0;  /* seL4_NoError */
}
