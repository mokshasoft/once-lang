/* seL4 BootInfo Primitives - C Backend Stubs
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

/* Mock BootInfo structure for testing */
static struct {
    int64_t untypedCount;
    int64_t untypedStart;
    int64_t initThreadTCB;
    int64_t initThreadCNode;
    int64_t initThreadVSpace;
    int64_t userImageFrames;
    int64_t domainInfo;
} mock_bootinfo = {
    .untypedCount = 5,       /* 5 untyped regions */
    .untypedStart = 20,      /* Untyped caps start at slot 20 */
    .initThreadTCB = 1,
    .initThreadCNode = 2,
    .initThreadVSpace = 3,
    .userImageFrames = 10,
    .domainInfo = 0
};

/* Mock untyped descriptors */
static struct {
    int64_t paddr;
    int64_t sizeBits;
    int64_t isDevice;
} mock_untypeds[] = {
    { 0x10000000, 20, 0 },   /* 1MB RAM at 0x10000000 */
    { 0x10100000, 18, 0 },   /* 256KB RAM */
    { 0x10140000, 16, 0 },   /* 64KB RAM */
    { 0x10150000, 14, 0 },   /* 16KB RAM */
    { 0x10154000, 12, 0 },   /* 4KB RAM */
};

/* Mock IPC buffer address */
static int64_t mock_ipc_buffer = 0x20000000;

/* BootInfo access functions */

void* once_getBootInfo(void* x) {
    (void)x;
    return (void*)&mock_bootinfo;
}

void* once_getIPCBuffer(void* x) {
    (void)x;
    return (void*)mock_ipc_buffer;
}

void* once_bootinfo_untypedCount(void* bootinfo) {
    (void)bootinfo;
    return (void*)mock_bootinfo.untypedCount;
}

void* once_bootinfo_untypedStart(void* bootinfo) {
    (void)bootinfo;
    return (void*)mock_bootinfo.untypedStart;
}

void* once_bootinfo_initThreadTCB(void* bootinfo) {
    (void)bootinfo;
    return (void*)mock_bootinfo.initThreadTCB;
}

void* once_bootinfo_initThreadCNode(void* bootinfo) {
    (void)bootinfo;
    return (void*)mock_bootinfo.initThreadCNode;
}

void* once_bootinfo_initThreadVSpace(void* bootinfo) {
    (void)bootinfo;
    return (void*)mock_bootinfo.initThreadVSpace;
}

void* once_bootinfo_userImageFrames(void* bootinfo) {
    (void)bootinfo;
    return (void*)mock_bootinfo.userImageFrames;
}

void* once_bootinfo_domainInfo(void* bootinfo) {
    (void)bootinfo;
    return (void*)mock_bootinfo.domainInfo;
}

/* Helper to build 3-tuple as nested pairs: ((paddr, sizeBits), isDevice) */
static OncePair make_tuple3(int64_t a, int64_t b, int64_t c) {
    static OncePair p1, p2;
    p1 = (OncePair){ .fst = (void*)a, .snd = (void*)b };
    p2 = (OncePair){ .fst = &p1, .snd = (void*)c };
    return p2;
}

OncePair once_bootinfo_getUntyped(OncePair args) {
    /* args is (bootinfo, index) */
    int64_t index = (int64_t)args.snd;

    if (index >= 0 && index < 5) {
        return make_tuple3(
            mock_untypeds[index].paddr,
            mock_untypeds[index].sizeBits,
            mock_untypeds[index].isDevice
        );
    }
    /* Return invalid for out-of-bounds */
    return make_tuple3(0, 0, 1);  /* isDevice=1 marks as unusable */
}
