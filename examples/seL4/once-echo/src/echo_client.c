/*
 * Once Echo Client
 *
 * Sends messages to the echo server and verifies the responses.
 * Uses seL4_CallWithMRs for RPC-style send + wait for reply.
 *
 * Note: Uses WithMRs variants to avoid needing IPC buffer setup.
 */

#include <sel4/sel4.h>

/* Endpoint slot - same as SLOT_ENDPOINT in main.c */
#define CLIENT_ENDPOINT 512

/* Number of echo tests to run */
#define NUM_TESTS 10

/* Simple debug print using seL4_DebugPutChar (works without IPC buffer) */
static void debug_puts(const char *s) {
    while (*s) {
        seL4_DebugPutChar(*s++);
    }
}

/*
 * Echo client main
 *
 * Sends test messages to the echo server and verifies
 * that the responses match what was sent.
 */
void echo_client_main(void) {
    seL4_MessageInfo_t info;
    int passed = 0;
    int failed = 0;

    debug_puts("Echo client started\n");

    for (int i = 0; i < NUM_TESTS; i++) {
        /* Build test message with unique values */
        seL4_Word v0 = 42 + i;
        seL4_Word v1 = 100 + i;
        seL4_Word v2 = 255;
        seL4_Word v3 = 1000 + i * 10;

        /* Message registers - will be filled with reply */
        seL4_Word mr0 = v0, mr1 = v1, mr2 = v2, mr3 = v3;

        /* Build message info: 4 message registers, no capabilities */
        info = seL4_MessageInfo_new(0, 0, 0, 4);

        /* Call server and wait for reply */
        info = seL4_CallWithMRs(CLIENT_ENDPOINT, info, &mr0, &mr1, &mr2, &mr3);

        /* Verify echo (mr0-mr3 now contain reply values) */
        if (mr0 == v0 && mr1 == v1 && mr2 == v2 && mr3 == v3) {
            passed++;
            debug_puts(".");
        } else {
            failed++;
            debug_puts("F");
        }
    }

    /* Report results */
    debug_puts("\n=== Echo Test Results ===\n");
    if (failed == 0) {
        debug_puts("All tests passed!\n");
    } else {
        debug_puts("Some tests failed\n");
    }
    debug_puts("=========================\n");

    /* Client done - just yield forever */
    while (1) {
        seL4_Yield();
    }
}
