/* seL4 TCB (Thread Control Block) Primitives - Real Implementation
 *
 * Calls the actual seL4 libsel4 functions for thread management.
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
 * Tuple unpacking helpers - Once tuples are left-nested
 */

static inline void unpack3(OncePair args, intptr_t *a, intptr_t *b, intptr_t *c) {
    *c = (intptr_t)args.snd;
    OncePair *p1 = (OncePair*)args.fst;
    *b = (intptr_t)p1->snd;
    *a = (intptr_t)p1->fst;
}

static inline void unpack4(OncePair args, intptr_t *a, intptr_t *b, intptr_t *c, intptr_t *d) {
    *d = (intptr_t)args.snd;
    OncePair *p2 = (OncePair*)args.fst;
    *c = (intptr_t)p2->snd;
    OncePair *p1 = (OncePair*)p2->fst;
    *b = (intptr_t)p1->snd;
    *a = (intptr_t)p1->fst;
}

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
 * TCB Primitives - Real implementations
 * ======================================================================== */

/* seL4_TCB_Configure:
 * Args: (tcb, faultEP, cspaceRoot, cspaceData, vspaceRoot, vspaceData, ipcBuffer, ipcBufferFrame)
 * Returns: error code */
void* once_seL4_TCB_Configure(OncePair args) {
    intptr_t tcb, faultEP, cspaceRoot, cspaceData;
    intptr_t vspaceRoot, vspaceData, ipcBuffer, ipcBufferFrame;
    unpack8(args, &tcb, &faultEP, &cspaceRoot, &cspaceData,
            &vspaceRoot, &vspaceData, &ipcBuffer, &ipcBufferFrame);

    seL4_Error err = seL4_TCB_Configure(
        (seL4_TCB)tcb,
        (seL4_CPtr)faultEP,
        (seL4_CNode)cspaceRoot,
        (seL4_Word)cspaceData,
        (seL4_CPtr)vspaceRoot,
        (seL4_Word)vspaceData,
        (seL4_Word)ipcBuffer,
        (seL4_CPtr)ipcBufferFrame
    );
    return (void*)(intptr_t)err;
}

/* seL4_TCB_SetPriority:
 * Args: (tcb, authority, priority)
 * Returns: error code */
void* once_seL4_TCB_SetPriority(OncePair args) {
    intptr_t tcb, authority, priority;
    unpack3(args, &tcb, &authority, &priority);

    seL4_Error err = seL4_TCB_SetPriority(
        (seL4_TCB)tcb,
        (seL4_TCB)authority,
        (seL4_Word)priority
    );
    return (void*)(intptr_t)err;
}

/* seL4_TCB_SetMCPriority:
 * Args: (tcb, authority, mcp)
 * Returns: error code */
void* once_seL4_TCB_SetMCPriority(OncePair args) {
    intptr_t tcb, authority, mcp;
    unpack3(args, &tcb, &authority, &mcp);

    seL4_Error err = seL4_TCB_SetMCPriority(
        (seL4_TCB)tcb,
        (seL4_TCB)authority,
        (seL4_Word)mcp
    );
    return (void*)(intptr_t)err;
}

/* seL4_TCB_SetSchedParams:
 * Args: (tcb, authority, mcp, priority)
 * Returns: error code */
void* once_seL4_TCB_SetSchedParams(OncePair args) {
    intptr_t tcb, authority, mcp, priority;
    unpack4(args, &tcb, &authority, &mcp, &priority);

    seL4_Error err = seL4_TCB_SetSchedParams(
        (seL4_TCB)tcb,
        (seL4_TCB)authority,
        (seL4_Word)mcp,
        (seL4_Word)priority
    );
    return (void*)(intptr_t)err;
}

/* seL4_TCB_SetIPCBuffer:
 * Args: (tcb, ipcBuffer, ipcBufferFrame)
 * Returns: error code */
void* once_seL4_TCB_SetIPCBuffer(OncePair args) {
    intptr_t tcb, ipcBuffer, ipcBufferFrame;
    unpack3(args, &tcb, &ipcBuffer, &ipcBufferFrame);

    seL4_Error err = seL4_TCB_SetIPCBuffer(
        (seL4_TCB)tcb,
        (seL4_Word)ipcBuffer,
        (seL4_CPtr)ipcBufferFrame
    );
    return (void*)(intptr_t)err;
}

/* seL4_TCB_SetSpace:
 * Args: (tcb, faultEP, cspaceRoot, cspaceData, vspaceRoot, vspaceData)
 * Returns: error code */
void* once_seL4_TCB_SetSpace(OncePair args) {
    intptr_t tcb, faultEP, cspaceRoot, cspaceData, vspaceRoot, vspaceData;
    unpack6(args, &tcb, &faultEP, &cspaceRoot, &cspaceData, &vspaceRoot, &vspaceData);

    seL4_Error err = seL4_TCB_SetSpace(
        (seL4_TCB)tcb,
        (seL4_CPtr)faultEP,
        (seL4_CNode)cspaceRoot,
        (seL4_Word)cspaceData,
        (seL4_CPtr)vspaceRoot,
        (seL4_Word)vspaceData
    );
    return (void*)(intptr_t)err;
}

/* seL4_TCB_Resume:
 * Args: tcb
 * Returns: error code */
void* once_seL4_TCB_Resume(void* tcb) {
    seL4_Error err = seL4_TCB_Resume((seL4_TCB)(intptr_t)tcb);
    return (void*)(intptr_t)err;
}

/* seL4_TCB_Suspend:
 * Args: tcb
 * Returns: error code */
void* once_seL4_TCB_Suspend(void* tcb) {
    seL4_Error err = seL4_TCB_Suspend((seL4_TCB)(intptr_t)tcb);
    return (void*)(intptr_t)err;
}

/* seL4_TCB_WriteRegisters:
 * Args: (tcb, resume, arch, count, regs)
 * Note: regs is a pointer to seL4_UserContext
 * Returns: error code */
void* once_seL4_TCB_WriteRegisters(OncePair args) {
    intptr_t tcb, resume, arch, count, regs;
    unpack5(args, &tcb, &resume, &arch, &count, &regs);

    seL4_Error err = seL4_TCB_WriteRegisters(
        (seL4_TCB)tcb,
        (seL4_Bool)resume,
        (seL4_Uint8)arch,
        (seL4_Word)count,
        (seL4_UserContext*)regs
    );
    return (void*)(intptr_t)err;
}

/* seL4_TCB_ReadRegisters:
 * Args: (tcb, suspend, arch, count, regs)
 * Returns: error code */
void* once_seL4_TCB_ReadRegisters(OncePair args) {
    intptr_t tcb, suspend, arch, count, regs;
    unpack5(args, &tcb, &suspend, &arch, &count, &regs);

    seL4_Error err = seL4_TCB_ReadRegisters(
        (seL4_TCB)tcb,
        (seL4_Bool)suspend,
        (seL4_Uint8)arch,
        (seL4_Word)count,
        (seL4_UserContext*)regs
    );
    return (void*)(intptr_t)err;
}
