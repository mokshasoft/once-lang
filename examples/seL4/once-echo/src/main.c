/*
 * Once Echo Server - seL4 Entry Point
 *
 * This is the main entry point for the Once Echo server running on seL4.
 * It initializes the seL4 environment and calls the Once-generated main function.
 */

#include <stdio.h>
#include <sel4/sel4.h>
#include <sel4platsupport/bootinfo.h>

/* Include Once-generated header for types */
#include "echo_server.h"

/* seL4 IPC primitives - stub implementations for now */
OncePair once_seL4_Recv(OncePair args) {
    seL4_Word sender_badge;
    seL4_Word dest = (seL4_Word)args.fst;

    /* Receive message on endpoint */
    seL4_MessageInfo_t info = seL4_Recv(dest, &sender_badge);

    /* Return (badge, msgInfo, mr0, mr1, mr2, mr3) as nested pairs */
    static OncePair p1, p2, p3, p4, p5;
    p1 = (OncePair){ .fst = (void*)sender_badge, .snd = (void*)info.words[0] };
    p2 = (OncePair){ .fst = &p1, .snd = (void*)seL4_GetMR(0) };
    p3 = (OncePair){ .fst = &p2, .snd = (void*)seL4_GetMR(1) };
    p4 = (OncePair){ .fst = &p3, .snd = (void*)seL4_GetMR(2) };
    p5 = (OncePair){ .fst = &p4, .snd = (void*)seL4_GetMR(3) };
    return p5;
}

void* once_seL4_Yield(void* x) {
    (void)x;
    seL4_Yield();
    return NULL;
}

int main(void) {
    printf("Once Echo Server starting...\n");

    /* Call Once-generated main */
    once_main(NULL);

    /* Should never reach here */
    printf("Once Echo Server exited unexpectedly\n");
    return 0;
}
