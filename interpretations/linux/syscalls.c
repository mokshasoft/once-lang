/* Linux interpretation - C backend */

#include <stdlib.h>
#include <stdio.h>

void* exit0(void* x) {
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

/* TODO: Replace with String type */
void* hello(void* x) {
    (void)x;
    puts("Hello for Once");
    return ((void*)0);
}
