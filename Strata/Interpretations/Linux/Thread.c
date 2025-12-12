/* Linux interpretation - Threading using raw syscalls
 *
 * Implements thread operations using raw Linux syscalls (clone, futex).
 * Does NOT use pthread or glibc's clone() wrapper.
 *
 * Based on techniques from:
 * - https://nullprogram.com/blog/2015/05/15/ (Raw Linux Threads)
 * - https://nullprogram.com/blog/2023/03/23/ (Practical libc-free threading)
 *
 * Architecture: x86_64 (inline assembly is architecture-specific)
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <stdlib.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <stdatomic.h>
#include <signal.h>

/* Linux-specific headers for threading */
#ifdef __linux__
#include <linux/futex.h>
#endif

/* Clone flags */
#ifndef CLONE_VM
#define CLONE_VM 0x00000100
#endif

/* Futex operations */
#ifndef FUTEX_WAIT
#define FUTEX_WAIT 0
#define FUTEX_WAKE 1
#endif

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
#endif

/* Thread stack size (4MB default, same as pthread default) */
#define THREAD_STACK_SIZE (4 * 1024 * 1024)

/* Thread handle structure */
typedef struct {
    int64_t tid;           /* Thread ID from clone() */
    _Atomic int32_t done;  /* Futex: 0 = running, 1 = done */
    void* stack;           /* Stack pointer for cleanup */
} ThreadHandle;

/*========================================================================
 * Internal: Raw clone with function pointer (x86_64)
 *========================================================================*/

/* Thread wrapper that signals completion after user function returns */
typedef struct {
    void* user_fn;
    ThreadHandle* handle;
} ThreadArgs;

static void thread_wrapper(void* arg) {
    ThreadArgs* args = (ThreadArgs*)arg;
    ThreadHandle* handle = args->handle;

    /* Call the user's thread function */
    void* (*fn)(void*) = (void* (*)(void*))args->user_fn;
    fn(NULL);

    /* Signal completion via futex */
    atomic_store(&handle->done, 1);
    syscall(SYS_futex, &handle->done, FUTEX_WAKE, 1, NULL, NULL, 0);
    /* Don't return - child will exit via assembly below */
}

/* Raw clone syscall with function pointer (x86_64)
 *
 * This implements what glibc's clone() wrapper does, but using only
 * raw syscalls and inline assembly. The key insight is:
 *
 * 1. Before clone: push fn and arg onto the NEW stack
 * 2. Call clone syscall with the prepared stack
 * 3. After clone returns 0 (in child): pop fn/arg and call fn(arg)
 * 4. Child exits via syscall, never returns
 *
 * This avoids any glibc dependency for thread creation.
 */
static pid_t raw_clone_with_fn(void (*fn)(void*), void* stack_top, int flags, void* arg) {
    pid_t ret;

    /* Prepare child's stack: push arg and fn (stack grows down) */
    void** sp = (void**)stack_top;
    *--sp = arg;
    *--sp = (void*)fn;

    __asm__ volatile(
        "syscall\n\t"              /* clone(flags, stack) */
        "test %%rax, %%rax\n\t"    /* child has rax=0 */
        "jnz 1f\n\t"               /* parent jumps to end */
        /* Child execution path */
        "pop %%rax\n\t"            /* fn */
        "pop %%rdi\n\t"            /* arg */
        "call *%%rax\n\t"          /* fn(arg) */
        "mov $60, %%eax\n\t"       /* SYS_exit */
        "xor %%edi, %%edi\n\t"     /* exit(0) */
        "syscall\n\t"
        "1:\n\t"
        : "=a"(ret)
        : "a"(SYS_clone), "D"(flags), "S"(sp), "d"(0), "r"((long)0), "r"((long)0)
        : "rcx", "r11", "memory"
    );

    return ret;
}

/*========================================================================
 * Thread Creation
 *========================================================================*/

OnceBuffer once_thread_spawn(void* func) {
    /* Allocate thread handle (shared between parent and child via CLONE_VM) */
    ThreadHandle* handle = (ThreadHandle*)malloc(sizeof(ThreadHandle));
    if (!handle) {
        return (OnceBuffer){ .data = NULL, .len = 0 };
    }

    /* Allocate stack via mmap */
    void* stack = mmap(NULL, THREAD_STACK_SIZE,
                       PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK,
                       -1, 0);
    if (stack == MAP_FAILED) {
        free(handle);
        return (OnceBuffer){ .data = NULL, .len = 0 };
    }

    /* Initialize handle */
    handle->stack = stack;
    atomic_store(&handle->done, 0);

    /* Prepare thread args on the stack (will be passed to wrapper) */
    ThreadArgs* args = (ThreadArgs*)stack;  /* Put at base of stack region */
    args->user_fn = func;
    args->handle = handle;

    /* Stack grows down; clone needs pointer to top */
    void* stack_top = (char*)stack + THREAD_STACK_SIZE;

    /* Clone with shared address space (CLONE_VM) and SIGCHLD for waitpid */
    pid_t tid = raw_clone_with_fn(thread_wrapper, stack_top, CLONE_VM | SIGCHLD, args);

    if (tid < 0) {
        munmap(stack, THREAD_STACK_SIZE);
        free(handle);
        return (OnceBuffer){ .data = NULL, .len = 0 };
    }

    handle->tid = tid;
    return (OnceBuffer){ .data = handle, .len = sizeof(ThreadHandle) };
}

void* once_thread_join(OnceBuffer handle_buf) {
    ThreadHandle* handle = (ThreadHandle*)handle_buf.data;
    if (!handle) return NULL;

    /* Wait for thread completion using futex */
    while (atomic_load(&handle->done) == 0) {
        syscall(SYS_futex, &handle->done, FUTEX_WAIT, 0, NULL, NULL, 0);
    }

    /* Wait for child process to exit (reap zombie) */
    waitpid(handle->tid, NULL, 0);

    /* Free resources */
    if (handle->stack) {
        munmap(handle->stack, THREAD_STACK_SIZE);
    }
    free(handle);

    return NULL;
}

void* once_thread_detach(void* func) {
    /* Spawn without keeping handle */
    OnceBuffer handle = once_thread_spawn(func);
    /* Don't free - thread will clean up when it exits */
    (void)handle;
    return NULL;
}

/*========================================================================
 * Synchronization Primitives
 *========================================================================*/

/* Mutex: simple futex-based spinlock
 * State: 0 = unlocked, 1 = locked
 */
OnceBuffer once_mutex_init(void* x) {
    (void)x;
    int32_t* mutex = (int32_t*)malloc(sizeof(int32_t));
    *mutex = 0;  /* Unlocked */
    return (OnceBuffer){ .data = mutex, .len = sizeof(int32_t) };
}

void* once_mutex_lock(OnceBuffer mutex_buf) {
    _Atomic int32_t* mutex = (_Atomic int32_t*)mutex_buf.data;

    while (1) {
        /* Try to acquire: 0 -> 1 */
        int32_t expected = 0;
        if (atomic_compare_exchange_weak(mutex, &expected, 1)) {
            return NULL;  /* Acquired */
        }
        /* Wait until possibly unlocked */
        syscall(SYS_futex, mutex, FUTEX_WAIT, 1, NULL, NULL, 0);
    }
}

void* once_mutex_unlock(OnceBuffer mutex_buf) {
    _Atomic int32_t* mutex = (_Atomic int32_t*)mutex_buf.data;

    atomic_store(mutex, 0);  /* Unlock */
    syscall(SYS_futex, mutex, FUTEX_WAKE, 1, NULL, NULL, 0);  /* Wake one waiter */

    return NULL;
}

/* Condition variable: uses mutex + futex */
typedef struct {
    _Atomic int32_t seq;  /* Sequence number for spurious wakeup detection */
} CondVar;

OnceBuffer once_cond_init(void* x) {
    (void)x;
    CondVar* cond = (CondVar*)malloc(sizeof(CondVar));
    atomic_store(&cond->seq, 0);
    return (OnceBuffer){ .data = cond, .len = sizeof(CondVar) };
}

void* once_cond_wait(OnceBuffer cond_buf, OnceBuffer mutex_buf) {
    CondVar* cond = (CondVar*)cond_buf.data;
    int32_t seq = atomic_load(&cond->seq);

    /* Release mutex while waiting */
    once_mutex_unlock(mutex_buf);

    /* Wait for signal (seq to change) */
    syscall(SYS_futex, &cond->seq, FUTEX_WAIT, seq, NULL, NULL, 0);

    /* Reacquire mutex */
    once_mutex_lock(mutex_buf);

    return NULL;
}

void* once_cond_signal(OnceBuffer cond_buf) {
    CondVar* cond = (CondVar*)cond_buf.data;

    atomic_fetch_add(&cond->seq, 1);  /* Change sequence */
    syscall(SYS_futex, &cond->seq, FUTEX_WAKE, 1, NULL, NULL, 0);  /* Wake one */

    return NULL;
}

void* once_cond_broadcast(OnceBuffer cond_buf) {
    CondVar* cond = (CondVar*)cond_buf.data;

    atomic_fetch_add(&cond->seq, 1);  /* Change sequence */
    syscall(SYS_futex, &cond->seq, FUTEX_WAKE, INT32_MAX, NULL, NULL, 0);  /* Wake all */

    return NULL;
}

/*========================================================================
 * Atomic Operations
 *========================================================================*/

int64_t once_atomic_cas(OnceBuffer addr_buf, int64_t expected, int64_t new_val) {
    _Atomic int64_t* addr = (_Atomic int64_t*)addr_buf.data;
    int64_t exp = expected;
    atomic_compare_exchange_strong(addr, &exp, new_val);
    return exp;  /* Return previous value */
}

int64_t once_atomic_add(OnceBuffer addr_buf, int64_t delta) {
    _Atomic int64_t* addr = (_Atomic int64_t*)addr_buf.data;
    return atomic_fetch_add(addr, delta);
}

void* once_memory_barrier(void* x) {
    (void)x;
    atomic_thread_fence(memory_order_seq_cst);
    return NULL;
}
