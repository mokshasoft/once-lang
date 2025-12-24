/* seL4 CNode (Capability Node) Primitives - Real Implementation
 *
 * Calls the actual seL4 libsel4 functions for capability management.
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
 * Tuple unpacking helpers
 */

static inline void unpack3(OncePair args, intptr_t *a, intptr_t *b, intptr_t *c) {
    *c = (intptr_t)args.snd;
    OncePair *p1 = (OncePair*)args.fst;
    *b = (intptr_t)p1->snd;
    *a = (intptr_t)p1->fst;
}

static inline void unpack7(OncePair args, intptr_t *a, intptr_t *b, intptr_t *c,
                           intptr_t *d, intptr_t *e, intptr_t *f, intptr_t *g) {
    *g = (intptr_t)args.snd;
    OncePair *p5 = (OncePair*)args.fst;
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
 * CNode Primitives - Real implementations
 * ======================================================================== */

/* seL4_CNode_Copy:
 * Args: (destRoot, destIndex, destDepth, srcRoot, srcIndex, srcDepth, rights)
 * Returns: error code */
void* once_seL4_CNode_Copy(OncePair args) {
    intptr_t destRoot, destIndex, destDepth;
    intptr_t srcRoot, srcIndex, srcDepth, rights;
    unpack7(args, &destRoot, &destIndex, &destDepth,
            &srcRoot, &srcIndex, &srcDepth, &rights);

    seL4_Error err = seL4_CNode_Copy(
        (seL4_CNode)destRoot,
        (seL4_Word)destIndex,
        (seL4_Uint8)destDepth,
        (seL4_CNode)srcRoot,
        (seL4_Word)srcIndex,
        (seL4_Uint8)srcDepth,
        (seL4_CapRights_t){ .words = { (seL4_Word)rights } }
    );
    return (void*)(intptr_t)err;
}

/* seL4_CNode_Mint:
 * Args: (destRoot, destIndex, destDepth, srcRoot, srcIndex, srcDepth, rights, badge)
 * Returns: error code */
void* once_seL4_CNode_Mint(OncePair args) {
    intptr_t destRoot, destIndex, destDepth;
    intptr_t srcRoot, srcIndex, srcDepth, rights, badge;
    unpack8(args, &destRoot, &destIndex, &destDepth,
            &srcRoot, &srcIndex, &srcDepth, &rights, &badge);

    seL4_Error err = seL4_CNode_Mint(
        (seL4_CNode)destRoot,
        (seL4_Word)destIndex,
        (seL4_Uint8)destDepth,
        (seL4_CNode)srcRoot,
        (seL4_Word)srcIndex,
        (seL4_Uint8)srcDepth,
        (seL4_CapRights_t){ .words = { (seL4_Word)rights } },
        (seL4_Word)badge
    );
    return (void*)(intptr_t)err;
}

/* seL4_CNode_Move:
 * Args: (destRoot, destIndex, destDepth, srcRoot, srcIndex, srcDepth)
 * Returns: error code */
void* once_seL4_CNode_Move(OncePair args) {
    intptr_t destRoot, destIndex, destDepth;
    intptr_t srcRoot, srcIndex, srcDepth;

    /* 6-tuple unpack */
    srcDepth = (intptr_t)args.snd;
    OncePair *p4 = (OncePair*)args.fst;
    srcIndex = (intptr_t)p4->snd;
    OncePair *p3 = (OncePair*)p4->fst;
    srcRoot = (intptr_t)p3->snd;
    OncePair *p2 = (OncePair*)p3->fst;
    destDepth = (intptr_t)p2->snd;
    OncePair *p1 = (OncePair*)p2->fst;
    destIndex = (intptr_t)p1->snd;
    destRoot = (intptr_t)p1->fst;

    seL4_Error err = seL4_CNode_Move(
        (seL4_CNode)destRoot,
        (seL4_Word)destIndex,
        (seL4_Uint8)destDepth,
        (seL4_CNode)srcRoot,
        (seL4_Word)srcIndex,
        (seL4_Uint8)srcDepth
    );
    return (void*)(intptr_t)err;
}

/* seL4_CNode_Delete:
 * Args: (root, index, depth)
 * Returns: error code */
void* once_seL4_CNode_Delete(OncePair args) {
    intptr_t root, index, depth;
    unpack3(args, &root, &index, &depth);

    seL4_Error err = seL4_CNode_Delete(
        (seL4_CNode)root,
        (seL4_Word)index,
        (seL4_Uint8)depth
    );
    return (void*)(intptr_t)err;
}

/* seL4_CNode_Revoke:
 * Args: (root, index, depth)
 * Returns: error code */
void* once_seL4_CNode_Revoke(OncePair args) {
    intptr_t root, index, depth;
    unpack3(args, &root, &index, &depth);

    seL4_Error err = seL4_CNode_Revoke(
        (seL4_CNode)root,
        (seL4_Word)index,
        (seL4_Uint8)depth
    );
    return (void*)(intptr_t)err;
}

/* ========================================================================
 * Capability Rights Constants
 * ======================================================================== */

void* once_seL4_AllRights(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_AllRights.words[0];
}

void* once_seL4_CanRead(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CanRead.words[0];
}

void* once_seL4_CanWrite(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CanWrite.words[0];
}

void* once_seL4_CanGrant(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CanGrant.words[0];
}

void* once_seL4_CanGrantReply(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CanGrantReply.words[0];
}
