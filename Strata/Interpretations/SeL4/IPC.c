/* seL4 IPC Primitives - C Backend Stubs
 *
 * These are stub implementations for the C backend.
 * For actual seL4 usage, use the x86_64/arm64 assembly implementations.
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

/* 6-element tuple: ((((((a, b), c), d), e), f) */
typedef struct {
    int64_t elem0;
    int64_t elem1;
    int64_t elem2;
    int64_t elem3;
    int64_t elem4;
    int64_t elem5;
} OnceTuple6;

/* 5-element tuple for seL4_Call return */
typedef struct {
    int64_t elem0;
    int64_t elem1;
    int64_t elem2;
    int64_t elem3;
    int64_t elem4;
} OnceTuple5;

/* Helper to build 6-tuple as nested pairs */
static OncePair make_tuple6(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f) {
    /* Build left-nested: ((((((a, b), c), d), e), f) */
    static OncePair p1, p2, p3, p4, p5;
    p1 = (OncePair){ .fst = (void*)a, .snd = (void*)b };
    p2 = (OncePair){ .fst = &p1, .snd = (void*)c };
    p3 = (OncePair){ .fst = &p2, .snd = (void*)d };
    p4 = (OncePair){ .fst = &p3, .snd = (void*)e };
    p5 = (OncePair){ .fst = &p4, .snd = (void*)f };
    return p5;
}

/* Stub implementations - these won't work on real seL4 */

void* once_seL4_Send(OncePair args) {
    /* In real seL4, this would trap to kernel */
    (void)args;
    return NULL;
}

void* once_seL4_NBSend(OncePair args) {
    (void)args;
    return NULL;
}

OncePair once_seL4_Recv(OncePair args) {
    /* Returns (badge, msgInfo, mr0, mr1, mr2, mr3) */
    (void)args;
    return make_tuple6(0, 0, 0, 0, 0, 0);
}

OncePair once_seL4_NBRecv(OncePair args) {
    (void)args;
    return make_tuple6(0, 0, 0, 0, 0, 0);
}

OncePair once_seL4_Call(OncePair args) {
    /* Returns (msgInfo, mr0, mr1, mr2, mr3) */
    (void)args;
    static OncePair p1, p2, p3, p4;
    p1 = (OncePair){ .fst = (void*)0, .snd = (void*)0 };
    p2 = (OncePair){ .fst = &p1, .snd = (void*)0 };
    p3 = (OncePair){ .fst = &p2, .snd = (void*)0 };
    p4 = (OncePair){ .fst = &p3, .snd = (void*)0 };
    return p4;
}

void* once_seL4_Reply(OncePair args) {
    (void)args;
    return NULL;
}

OncePair once_seL4_ReplyRecv(OncePair args) {
    /* Returns (badge, msgInfo, mr0, mr1, mr2, mr3) */
    (void)args;
    return make_tuple6(0, 0, 0, 0, 0, 0);
}

void* once_seL4_Yield(void* x) {
    (void)x;
    return NULL;
}
