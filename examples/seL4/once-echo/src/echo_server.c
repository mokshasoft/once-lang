/*
 * Once Echo Server
 *
 * Receives messages on an endpoint and echoes them back.
 * Uses seL4_ReplyRecvWithMRs for efficient server loop.
 *
 * Note: Uses WithMRs variants to avoid needing IPC buffer setup.
 */

#include <sel4/sel4.h>

/* Endpoint slot - same as SLOT_ENDPOINT in main.c */
#define SERVER_ENDPOINT 512

/* Simple debug print using seL4_DebugPutChar (works without IPC buffer) */
static void debug_puts(const char *s) {
    while (*s) {
        seL4_DebugPutChar(*s++);
    }
}

/*
 * Echo server main loop
 *
 * Receives messages and echoes them back to the caller.
 * Uses ReplyRecvWithMRs for atomic reply + wait pattern.
 */
void echo_server_main(void) {
    seL4_Word sender_badge;
    seL4_MessageInfo_t info;
    seL4_Word mr0 = 0, mr1 = 0, mr2 = 0, mr3 = 0;

    debug_puts("Echo server started\n");

    /* First receive - no reply yet */
    info = seL4_RecvWithMRs(SERVER_ENDPOINT, &sender_badge, &mr0, &mr1, &mr2, &mr3);
    debug_puts("Server: First message received\n");

    /* Main server loop */
    while (1) {
        /* Echo: reply with same values and wait for next message */
        info = seL4_ReplyRecvWithMRs(SERVER_ENDPOINT, info, &sender_badge,
                                      &mr0, &mr1, &mr2, &mr3);
    }
}
