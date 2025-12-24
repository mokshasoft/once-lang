/* seL4 IPC Primitives - Real Implementation
 *
 * Calls the actual seL4 libsel4 functions.
 * Uses WithMRs variants to avoid IPC buffer dependencies.
 */

#include <sel4/sel4.h>
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

/*
 * Tuple unpacking helpers
 *
 * Once tuples are left-nested: (a,b,c,d) = (((a,b),c),d)
 * So for a 6-tuple (a,b,c,d,e,f):
 *   f = args.snd
 *   e = args.fst->snd
 *   d = args.fst->fst->snd
 *   c = args.fst->fst->fst->snd
 *   b = args.fst->fst->fst->fst->snd
 *   a = args.fst->fst->fst->fst->fst
 */

/* Unpack 2-tuple */
#define UNPACK2_1(p) ((intptr_t)((OncePair*)(p).fst)->fst)
#define UNPACK2_2(p) ((intptr_t)((OncePair*)(p).fst)->snd)

/* Unpack 6-tuple: (((((a,b),c),d),e),f) */
static inline void unpack6(OncePair args, intptr_t *a, intptr_t *b, intptr_t *c,
                           intptr_t *d, intptr_t *e, intptr_t *f) {
    *f = (intptr_t)args.snd;
    OncePair *p4 = (OncePair*)args.fst;
    *e = (intptr_t)p4->snd;
    OncePair *p3 = (OncePair*)p4->fst;
    *d = (intptr_t)p3->snd;
    OncePair *p2 = (OncePair*)p3->fst;
    *c = (intptr_t)p2->snd;
    OncePair *p1 = (OncePair*)p2->fst;
    *b = (intptr_t)p1->snd;
    *a = (intptr_t)p1->fst;
}

/* Unpack 5-tuple: ((((a,b),c),d),e) */
static inline void unpack5(OncePair args, intptr_t *a, intptr_t *b, intptr_t *c,
                           intptr_t *d, intptr_t *e) {
    *e = (intptr_t)args.snd;
    OncePair *p3 = (OncePair*)args.fst;
    *d = (intptr_t)p3->snd;
    OncePair *p2 = (OncePair*)p3->fst;
    *c = (intptr_t)p2->snd;
    OncePair *p1 = (OncePair*)p2->fst;
    *b = (intptr_t)p1->snd;
    *a = (intptr_t)p1->fst;
}

/* Unpack 7-tuple: ((((((a,b),c),d),e),f),g) */
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

/*
 * Tuple packing helpers - build left-nested pairs
 * Uses thread-local storage to avoid static variable issues
 */

static __thread OncePair pack_buf[10];

/* Build 5-tuple: ((((a,b),c),d),e) */
static OncePair make_tuple5(intptr_t a, intptr_t b, intptr_t c, intptr_t d, intptr_t e) {
    pack_buf[0] = (OncePair){ .fst = (void*)a, .snd = (void*)b };
    pack_buf[1] = (OncePair){ .fst = &pack_buf[0], .snd = (void*)c };
    pack_buf[2] = (OncePair){ .fst = &pack_buf[1], .snd = (void*)d };
    pack_buf[3] = (OncePair){ .fst = &pack_buf[2], .snd = (void*)e };
    return pack_buf[3];
}

/* Build 6-tuple: (((((a,b),c),d),e),f) */
static OncePair make_tuple6(intptr_t a, intptr_t b, intptr_t c, intptr_t d,
                            intptr_t e, intptr_t f) {
    pack_buf[0] = (OncePair){ .fst = (void*)a, .snd = (void*)b };
    pack_buf[1] = (OncePair){ .fst = &pack_buf[0], .snd = (void*)c };
    pack_buf[2] = (OncePair){ .fst = &pack_buf[1], .snd = (void*)d };
    pack_buf[3] = (OncePair){ .fst = &pack_buf[2], .snd = (void*)e };
    pack_buf[4] = (OncePair){ .fst = &pack_buf[3], .snd = (void*)f };
    return pack_buf[4];
}

/* ========================================================================
 * IPC Primitives - Real implementations using WithMRs variants
 * ======================================================================== */

/* seL4_Send: (cap, msgInfo, mr0, mr1, mr2, mr3) -> Unit */
void* once_seL4_Send(OncePair args) {
    intptr_t cap, msgInfo, mr0, mr1, mr2, mr3;
    unpack6(args, &cap, &msgInfo, &mr0, &mr1, &mr2, &mr3);

    seL4_MessageInfo_t info = { .words = { (seL4_Word)msgInfo } };
    seL4_SendWithMRs((seL4_CPtr)cap, info,
                     (seL4_Word*)&mr0, (seL4_Word*)&mr1,
                     (seL4_Word*)&mr2, (seL4_Word*)&mr3);
    return NULL;
}

/* seL4_NBSend: (cap, msgInfo, mr0, mr1, mr2, mr3) -> Unit */
void* once_seL4_NBSend(OncePair args) {
    intptr_t cap, msgInfo, mr0, mr1, mr2, mr3;
    unpack6(args, &cap, &msgInfo, &mr0, &mr1, &mr2, &mr3);

    seL4_MessageInfo_t info = { .words = { (seL4_Word)msgInfo } };
    seL4_NBSendWithMRs((seL4_CPtr)cap, info,
                       (seL4_Word*)&mr0, (seL4_Word*)&mr1,
                       (seL4_Word*)&mr2, (seL4_Word*)&mr3);
    return NULL;
}

/* seL4_Recv: (src, reply) -> (badge, msgInfo, mr0, mr1, mr2, mr3) */
OncePair once_seL4_Recv(OncePair args) {
    intptr_t src = (intptr_t)((OncePair*)args.fst)->fst;
    /* reply slot ignored in non-MCS kernel */

    seL4_Word badge;
    seL4_Word mr0 = 0, mr1 = 0, mr2 = 0, mr3 = 0;
    seL4_MessageInfo_t info = seL4_RecvWithMRs((seL4_CPtr)src, &badge,
                                                &mr0, &mr1, &mr2, &mr3);

    return make_tuple6((intptr_t)badge, (intptr_t)info.words[0],
                       (intptr_t)mr0, (intptr_t)mr1, (intptr_t)mr2, (intptr_t)mr3);
}

/* seL4_NBRecv: (src, reply) -> (badge, msgInfo, mr0, mr1, mr2, mr3) */
OncePair once_seL4_NBRecv(OncePair args) {
    intptr_t src = (intptr_t)((OncePair*)args.fst)->fst;

    seL4_Word badge;
    /* Note: seL4_NBRecvWithMRs doesn't exist, use Poll which is the non-blocking variant */
    seL4_Word mr0 = 0, mr1 = 0, mr2 = 0, mr3 = 0;
    seL4_MessageInfo_t info = seL4_Poll((seL4_CPtr)src, &badge);

    /* Get message registers from IPC buffer if we got a message */
    if (seL4_MessageInfo_get_length(info) > 0) {
        mr0 = seL4_GetMR(0);
        if (seL4_MessageInfo_get_length(info) > 1) mr1 = seL4_GetMR(1);
        if (seL4_MessageInfo_get_length(info) > 2) mr2 = seL4_GetMR(2);
        if (seL4_MessageInfo_get_length(info) > 3) mr3 = seL4_GetMR(3);
    }

    return make_tuple6((intptr_t)badge, (intptr_t)info.words[0],
                       (intptr_t)mr0, (intptr_t)mr1, (intptr_t)mr2, (intptr_t)mr3);
}

/* seL4_Call: (cap, msgInfo, mr0, mr1, mr2, mr3) -> (msgInfo, mr0, mr1, mr2, mr3) */
OncePair once_seL4_Call(OncePair args) {
    intptr_t cap, msgInfo, mr0, mr1, mr2, mr3;
    unpack6(args, &cap, &msgInfo, &mr0, &mr1, &mr2, &mr3);

    seL4_MessageInfo_t info = { .words = { (seL4_Word)msgInfo } };
    seL4_Word w0 = (seL4_Word)mr0, w1 = (seL4_Word)mr1;
    seL4_Word w2 = (seL4_Word)mr2, w3 = (seL4_Word)mr3;

    info = seL4_CallWithMRs((seL4_CPtr)cap, info, &w0, &w1, &w2, &w3);

    return make_tuple5((intptr_t)info.words[0],
                       (intptr_t)w0, (intptr_t)w1, (intptr_t)w2, (intptr_t)w3);
}

/* seL4_Reply: (msgInfo, mr0, mr1, mr2, mr3) -> Unit */
void* once_seL4_Reply(OncePair args) {
    intptr_t msgInfo, mr0, mr1, mr2, mr3;
    unpack5(args, &msgInfo, &mr0, &mr1, &mr2, &mr3);

    seL4_MessageInfo_t info = { .words = { (seL4_Word)msgInfo } };
    seL4_ReplyWithMRs(info, (seL4_Word*)&mr0, (seL4_Word*)&mr1,
                      (seL4_Word*)&mr2, (seL4_Word*)&mr3);
    return NULL;
}

/* seL4_ReplyRecv: (src, msgInfo, mr0, mr1, mr2, mr3, reply)
 *              -> (badge, msgInfo, mr0, mr1, mr2, mr3) */
OncePair once_seL4_ReplyRecv(OncePair args) {
    intptr_t src, msgInfo, mr0, mr1, mr2, mr3, reply;
    unpack7(args, &src, &msgInfo, &mr0, &mr1, &mr2, &mr3, &reply);

    seL4_MessageInfo_t info = { .words = { (seL4_Word)msgInfo } };
    seL4_Word badge;
    seL4_Word w0 = (seL4_Word)mr0, w1 = (seL4_Word)mr1;
    seL4_Word w2 = (seL4_Word)mr2, w3 = (seL4_Word)mr3;

    info = seL4_ReplyRecvWithMRs((seL4_CPtr)src, info, &badge, &w0, &w1, &w2, &w3);

    return make_tuple6((intptr_t)badge, (intptr_t)info.words[0],
                       (intptr_t)w0, (intptr_t)w1, (intptr_t)w2, (intptr_t)w3);
}

/* seL4_Yield: Unit -> Unit */
void* once_seL4_Yield(void* x) {
    (void)x;
    seL4_Yield();
    return NULL;
}
