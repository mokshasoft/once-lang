/* Linux interpretation - File I/O convenience functions
 *
 * Higher-level file operations built on raw syscalls.
 * These provide a more convenient interface than raw fd_read/fd_write.
 *
 * String Convention:
 * OnceString stores both pointer and length, and is ALWAYS null-terminated.
 * This allows direct use with C library functions without malloc/copy overhead.
 */

#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
#endif

/*========================================================================
 * Output Operations
 *========================================================================*/

void* once_print(OnceString s) {
    fwrite(s.data, 1, s.len, stdout);
    return NULL;
}

void* once_println(OnceString s) {
    fwrite(s.data, 1, s.len, stdout);
    putchar('\n');
    return NULL;
}

void* once_err(OnceString s) {
    fwrite(s.data, 1, s.len, stderr);
    return NULL;
}

void* once_errln(OnceString s) {
    fwrite(s.data, 1, s.len, stderr);
    fputc('\n', stderr);
    return NULL;
}

void* once_putc(int64_t c) {
    putchar((int)c);
    return NULL;
}

void* once_flush(void* x) {
    (void)x;
    fflush(stdout);
    return NULL;
}

/*========================================================================
 * Input Operations
 *========================================================================*/

int64_t once_getc(void* x) {
    (void)x;
    return (int64_t)getchar();
}

int64_t once_getline(OnceBuffer buf, int64_t maxlen) {
    if (maxlen <= 0 || buf.data == NULL) {
        return -1;
    }

    char* ptr = (char*)buf.data;
    int64_t count = 0;
    int c;

    while (count < maxlen - 1) {
        c = getchar();
        if (c == EOF) {
            if (count == 0) return -1;  /* EOF with no data */
            break;
        }
        if (c == '\n') {
            break;  /* Don't include newline */
        }
        ptr[count++] = (char)c;
    }

    ptr[count] = '\0';  /* Null-terminate */
    return count;
}

/*========================================================================
 * File Reading Helpers
 *========================================================================*/

int64_t once_readfile(OnceString path, OnceBuffer buf, int64_t maxlen) {
    int fd = open(path.data, O_RDONLY);
    if (fd < 0) {
        return -1;
    }

    ssize_t total = 0;
    ssize_t remaining = (ssize_t)maxlen;
    char* ptr = (char*)buf.data;

    while (remaining > 0) {
        ssize_t n = read(fd, ptr + total, (size_t)remaining);
        if (n < 0) {
            close(fd);
            return -1;
        }
        if (n == 0) {
            break;  /* EOF */
        }
        total += n;
        remaining -= n;
    }

    close(fd);
    return (int64_t)total;
}

int64_t once_filesize(OnceString path) {
    struct stat st;
    if (stat(path.data, &st) < 0) {
        return -1;
    }
    return (int64_t)st.st_size;
}
