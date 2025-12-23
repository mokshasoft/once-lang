/* seL4 TCB (Thread Control Block) Primitives - C Backend Stubs
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

/* seL4_TCB_Configure stub
 *
 * Arguments (as nested pairs):
 *   tcb, faultEP, cspaceRoot, cspaceData, vspaceRoot, vspaceData, ipcBuffer, ipcBufferFrame
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_Configure(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_SetPriority stub
 *
 * Arguments (as nested pairs):
 *   tcb, authority, priority
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_SetPriority(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_SetMCPriority stub
 *
 * Arguments (as nested pairs):
 *   tcb, authority, mcp
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_SetMCPriority(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_SetSchedParams stub
 *
 * Arguments (as nested pairs):
 *   tcb, authority, mcp, priority
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_SetSchedParams(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_SetIPCBuffer stub
 *
 * Arguments (as nested pairs):
 *   tcb, ipcBuffer, ipcBufferFrame
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_SetIPCBuffer(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_SetSpace stub
 *
 * Arguments (as nested pairs):
 *   tcb, faultEP, cspaceRoot, cspaceData, vspaceRoot, vspaceData
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_SetSpace(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_Resume stub
 *
 * Arguments: tcb capability
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_Resume(void* tcb) {
    (void)tcb;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_Suspend stub
 *
 * Arguments: tcb capability
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_Suspend(void* tcb) {
    (void)tcb;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_WriteRegisters stub
 *
 * Arguments (as nested pairs):
 *   tcb, resume, arch, count, regs
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_WriteRegisters(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}

/* seL4_TCB_ReadRegisters stub
 *
 * Arguments (as nested pairs):
 *   tcb, suspend, arch, count, regs
 *
 * Returns: 0 (success)
 */
void* once_seL4_TCB_ReadRegisters(OncePair args) {
    (void)args;
    return (void*)0;  /* seL4_NoError */
}
