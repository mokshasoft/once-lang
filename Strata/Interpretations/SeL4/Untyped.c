/* seL4 Untyped Memory Primitives - Real Implementation
 *
 * Calls the actual seL4 libsel4 functions for memory management.
 */

#include <sel4/sel4.h>
#include <stdint.h>
#include <stddef.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
#endif

#ifndef ONCE_PAIR_DEFINED
#define ONCE_PAIR_DEFINED
typedef struct { void* fst; void* snd; } OncePair;
#endif

/*
 * Tuple unpacking helper
 */
static inline void unpack8(OncePair args, intptr_t *a, intptr_t *b, intptr_t *c,
                           intptr_t *d, intptr_t *e, intptr_t *f, intptr_t *g,
                           intptr_t *h) {
    *h = (intptr_t)args.snd;
    OncePair *p6 = (OncePair*)args.fst;
    *g = (intptr_t)p6->snd;
    OncePair *p5 = (OncePair*)p6->fst;
    *f = (intptr_t)p5->snd;
    OncePair *p4 = (OncePair*)p5->fst;
    *e = (intptr_t)p4->snd;
    OncePair *p3 = (OncePair*)p4->fst;
    *d = (intptr_t)p3->snd;
    OncePair *p2 = (OncePair*)p3->fst;
    *c = (intptr_t)p2->snd;
    OncePair *p1 = (OncePair*)p2->fst;
    *b = (intptr_t)p1->snd;
    *a = (intptr_t)p1->fst;
}

/* ========================================================================
 * Untyped Primitives - Real implementations
 * ======================================================================== */

/* seL4_Untyped_Retype:
 * Args: (untyped, objectType, sizeBits, root, nodeIndex, nodeDepth, nodeOffset, numObjects)
 * Returns: error code */
void* once_seL4_Untyped_Retype(OncePair args) {
    intptr_t untyped, objectType, sizeBits, root;
    intptr_t nodeIndex, nodeDepth, nodeOffset, numObjects;
    unpack8(args, &untyped, &objectType, &sizeBits, &root,
            &nodeIndex, &nodeDepth, &nodeOffset, &numObjects);

    seL4_Error err = seL4_Untyped_Retype(
        (seL4_Untyped)untyped,
        (seL4_Word)objectType,
        (seL4_Word)sizeBits,
        (seL4_CNode)root,
        (seL4_Word)nodeIndex,
        (seL4_Word)nodeDepth,
        (seL4_Word)nodeOffset,
        (seL4_Word)numObjects
    );
    return (void*)(intptr_t)err;
}
