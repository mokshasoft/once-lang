/* seL4 CNode (Capability Node) Primitives - C Backend Stubs
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

/* seL4_CNode_Copy stub
 *
 * Arguments (as nested pairs):
 *   destRoot, destIndex, destDepth, srcRoot, srcIndex, srcDepth, rights
 *
 * Returns: 0 (success)
 */
void* once_seL4_CNode_Copy(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_CNode_Mint stub
 *
 * Arguments (as nested pairs):
 *   destRoot, destIndex, destDepth, srcRoot, srcIndex, srcDepth, rights, badge
 *
 * Returns: 0 (success)
 */
void* once_seL4_CNode_Mint(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_CNode_Move stub
 *
 * Arguments (as nested pairs):
 *   destRoot, destIndex, destDepth, srcRoot, srcIndex, srcDepth, rights
 *
 * Returns: 0 (success)
 */
void* once_seL4_CNode_Move(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_CNode_Delete stub
 *
 * Arguments (as nested pairs):
 *   root, index, depth
 *
 * Returns: 0 (success)
 */
void* once_seL4_CNode_Delete(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_CNode_Revoke stub
 *
 * Arguments (as nested pairs):
 *   root, index, depth
 *
 * Returns: 0 (success)
 */
void* once_seL4_CNode_Revoke(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}
