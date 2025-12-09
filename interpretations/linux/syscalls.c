/* Linux interpretation - C backend */

#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>

/* OnceString type (encoding erased at runtime) */
typedef struct {
    const char* data;
    size_t len;
} OnceString;

void* once_exit0(void* x) {
    (void)x;
    exit(0);
    return ((void*)0);
}

void* once_exit(int x) {
    exit(x);
    return ((void*)0);
}

void* once_putchar(int c) {
    putchar(c);
    return ((void*)0);
}

int once_getchar(void* x) {
    (void)x;
    return getchar();
}

void* once_puts(OnceString s) {
    fwrite(s.data, 1, s.len, stdout);
    putchar('\n');
    return ((void*)0);
}
