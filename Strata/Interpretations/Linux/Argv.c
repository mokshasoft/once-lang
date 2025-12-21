/* Command-line argument access for Once
 *
 * C implementation of Argv.once primitives.
 * Reads /proc/self/cmdline at startup to get argc/argv.
 */

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
typedef struct { intptr_t fst; intptr_t snd; } OncePair;
typedef struct { int tag; intptr_t value; } OnceSum;
#endif

/* Storage for parsed arguments */
#define ONCE_MAX_ARGS 256
#define ONCE_CMDLINE_SIZE 4096

static int g_argc = 0;
static char* g_argv[ONCE_MAX_ARGS];
static char g_cmdline_buf[ONCE_CMDLINE_SIZE];

/* Initialize argv from /proc/self/cmdline */
__attribute__((constructor))
static void once_argv_init(void) {
    int fd = open("/proc/self/cmdline", O_RDONLY);
    if (fd < 0) return;

    ssize_t len = read(fd, g_cmdline_buf, ONCE_CMDLINE_SIZE - 1);
    close(fd);

    if (len <= 0) return;
    g_cmdline_buf[len] = '\0';

    /* Parse null-separated arguments */
    char* p = g_cmdline_buf;
    char* end = g_cmdline_buf + len;

    while (p < end && g_argc < ONCE_MAX_ARGS) {
        if (*p != '\0') {
            g_argv[g_argc++] = p;
            /* Skip to next null */
            while (p < end && *p != '\0') p++;
        }
        p++;  /* Skip the null terminator */
    }
}

/* argc: Get argument count */
int64_t once_argc(void* x) {
    (void)x;
    return (int64_t)g_argc;
}

/* argv: Get argument at index */
OnceString once_argv(int64_t idx) {
    OnceString result = { "", 0 };

    if (idx >= 0 && idx < g_argc) {
        result.data = g_argv[idx];
        result.len = strlen(g_argv[idx]);
    }

    return result;
}

/* argn: Get first argument as integer (convenience for benchmarks) */
int64_t once_argn(void* x) {
    (void)x;
    if (g_argc >= 2) {
        return (int64_t)atoll(g_argv[1]);
    }
    return 0;
}
