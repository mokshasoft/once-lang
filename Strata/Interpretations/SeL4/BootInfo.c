/* seL4 BootInfo Primitives - Real Implementation
 *
 * Accesses the actual seL4 BootInfo structure.
 */

#include <sel4/sel4.h>
#include <sel4platsupport/bootinfo.h>
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

/* Thread-local buffer for building tuples */
static __thread OncePair pack_buf[5];

/* Build 3-tuple: ((a, b), c) */
static OncePair make_tuple3(intptr_t a, intptr_t b, intptr_t c) {
    pack_buf[0] = (OncePair){ .fst = (void*)a, .snd = (void*)b };
    pack_buf[1] = (OncePair){ .fst = &pack_buf[0], .snd = (void*)c };
    return pack_buf[1];
}

/* ========================================================================
 * BootInfo Primitives - Real implementations
 * ======================================================================== */

/* Get BootInfo pointer from seL4 */
void* once_getBootInfo(void* x) {
    (void)x;
    return (void*)platsupport_get_bootinfo();
}

/* Get IPC buffer address */
void* once_getIPCBuffer(void* x) {
    (void)x;
    return (void*)seL4_GetIPCBuffer();
}

/* Get count of untyped regions */
void* once_bootinfo_untypedCount(void* bootinfo) {
    seL4_BootInfo *bi = (seL4_BootInfo*)bootinfo;
    return (void*)(intptr_t)(bi->untyped.end - bi->untyped.start);
}

/* Get starting slot of untyped caps */
void* once_bootinfo_untypedStart(void* bootinfo) {
    seL4_BootInfo *bi = (seL4_BootInfo*)bootinfo;
    return (void*)(intptr_t)bi->untyped.start;
}

/* Get initial thread's TCB cap */
void* once_bootinfo_initThreadTCB(void* bootinfo) {
    (void)bootinfo;
    return (void*)(intptr_t)seL4_CapInitThreadTCB;
}

/* Get initial thread's CNode cap */
void* once_bootinfo_initThreadCNode(void* bootinfo) {
    (void)bootinfo;
    return (void*)(intptr_t)seL4_CapInitThreadCNode;
}

/* Get initial thread's VSpace cap */
void* once_bootinfo_initThreadVSpace(void* bootinfo) {
    (void)bootinfo;
    return (void*)(intptr_t)seL4_CapInitThreadVSpace;
}

/* Get user image frames slot range */
void* once_bootinfo_userImageFrames(void* bootinfo) {
    seL4_BootInfo *bi = (seL4_BootInfo*)bootinfo;
    return (void*)(intptr_t)bi->userImageFrames.start;
}

/* Get domain info (not commonly used) */
void* once_bootinfo_domainInfo(void* bootinfo) {
    (void)bootinfo;
    return (void*)0;
}

/* Get untyped descriptor by index
 * Args: (bootinfo, index)
 * Returns: (paddr, (sizeBits, isDevice)) */
OncePair once_bootinfo_getUntyped(OncePair args) {
    seL4_BootInfo *bi = (seL4_BootInfo*)((OncePair*)args.fst)->fst;
    intptr_t index = (intptr_t)args.snd;

    seL4_Word count = bi->untyped.end - bi->untyped.start;
    if (index >= 0 && (seL4_Word)index < count) {
        seL4_UntypedDesc *desc = &bi->untypedList[index];
        return make_tuple3(
            (intptr_t)desc->paddr,
            (intptr_t)desc->sizeBits,
            (intptr_t)desc->isDevice
        );
    }
    /* Return invalid for out-of-bounds */
    return make_tuple3(0, 0, 1);  /* isDevice=1 marks as unusable */
}

/* ========================================================================
 * Well-known capability constants
 * ======================================================================== */

void* once_seL4_CapInitThreadTCB(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CapInitThreadTCB;
}

void* once_seL4_CapInitThreadCNode(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CapInitThreadCNode;
}

void* once_seL4_CapInitThreadVSpace(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CapInitThreadVSpace;
}

void* once_seL4_CapNull(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CapNull;
}

void* once_seL4_CapIRQControl(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CapIRQControl;
}

void* once_seL4_CapASIDControl(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CapASIDControl;
}

void* once_seL4_CapASIDPool(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CapASIDPool;
}

void* once_seL4_CapIOPortControl(void* x) {
    (void)x;
#ifdef CONFIG_ARCH_X86
    return (void*)(intptr_t)seL4_CapIOPortControl;
#else
    return (void*)0;
#endif
}

void* once_seL4_CapIOSpace(void* x) {
    (void)x;
#ifdef CONFIG_ARCH_X86
    return (void*)(intptr_t)seL4_CapIOSpace;
#else
    return (void*)0;
#endif
}

void* once_seL4_CapDomain(void* x) {
    (void)x;
    return (void*)(intptr_t)seL4_CapDomain;
}
