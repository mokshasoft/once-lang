/* Exit interpretation for testing */

#include <stdlib.h>

void* once_exit0(void* x) {
    (void)x;
    exit(0);
    return ((void*)0);
}
