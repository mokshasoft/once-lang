/*
 * Once Echo - seL4 Rootserver
 *
 * This rootserver:
 * 1. Creates an endpoint for IPC
 * 2. Creates two TCBs (server and client threads)
 * 3. Configures them to share our address space
 * 4. Sets their entry points and stacks
 * 5. Resumes both threads
 *
 * The server echoes messages back to the client.
 */

#include <stdio.h>
#include <string.h>
#include <sel4/sel4.h>
#include <sel4platsupport/bootinfo.h>

/* Forward declarations for thread entry points */
void echo_server_main(void);
void echo_client_main(void);

/* Slot assignments in the rootserver's CNode */
/* Use high slot numbers to avoid conflicts with bootinfo caps */
#define SLOT_ENDPOINT     512
#define SLOT_SERVER_TCB   513
#define SLOT_CLIENT_TCB   514

/* Stack size for child threads */
#define STACK_SIZE 4096

/* Static stacks for server and client threads */
static char server_stack[STACK_SIZE] __attribute__((aligned(16)));
static char client_stack[STACK_SIZE] __attribute__((aligned(16)));

/* The endpoint capability - shared between server and client */
/* Server and client both use SLOT_ENDPOINT since they share our CSpace */

/*
 * Find a suitable untyped memory region
 * Returns the capability slot or 0 if not found
 */
static seL4_CPtr find_untyped(seL4_BootInfo *info, seL4_Word size_bits) {
    for (seL4_Word i = 0; i < info->untyped.end - info->untyped.start; i++) {
        seL4_UntypedDesc *desc = &info->untypedList[i];
        if (!desc->isDevice && desc->sizeBits >= size_bits) {
            return info->untyped.start + i;
        }
    }
    return 0;
}

int main(void) {
    seL4_BootInfo *info = platsupport_get_bootinfo();
    seL4_Error err;

    printf("Once Echo Rootserver starting...\n");

    /* 1. Find untyped memory for allocations */
    /* We need: 1 endpoint (16 bytes) + 2 TCBs (2KB each) */
    seL4_CPtr ut = find_untyped(info, 12);  /* 4KB should be enough */
    if (ut == 0) {
        printf("ERROR: No suitable untyped memory found\n");
        return 1;
    }
    printf("Found untyped at slot %lu\n", (unsigned long)ut);

    /* 2. Create endpoint for IPC between server and client */
    err = seL4_Untyped_Retype(ut,
                              seL4_EndpointObject,
                              seL4_EndpointBits,
                              seL4_CapInitThreadCNode,
                              0,  /* node_index */
                              0,  /* node_depth */
                              SLOT_ENDPOINT,
                              1);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to create endpoint: %d\n", err);
        return 1;
    }
    printf("Created endpoint at slot %d\n", SLOT_ENDPOINT);

    /* 3. Create server TCB */
    err = seL4_Untyped_Retype(ut,
                              seL4_TCBObject,
                              seL4_TCBBits,
                              seL4_CapInitThreadCNode,
                              0, 0,
                              SLOT_SERVER_TCB,
                              1);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to create server TCB: %d\n", err);
        return 1;
    }
    printf("Created server TCB at slot %d\n", SLOT_SERVER_TCB);

    /* 4. Create client TCB */
    err = seL4_Untyped_Retype(ut,
                              seL4_TCBObject,
                              seL4_TCBBits,
                              seL4_CapInitThreadCNode,
                              0, 0,
                              SLOT_CLIENT_TCB,
                              1);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to create client TCB: %d\n", err);
        return 1;
    }
    printf("Created client TCB at slot %d\n", SLOT_CLIENT_TCB);

    /* 5. Configure server TCB - share our CSpace and VSpace */
    err = seL4_TCB_Configure(SLOT_SERVER_TCB,
                             seL4_CapNull,              /* fault_ep */
                             seL4_CapInitThreadCNode,   /* cspace_root */
                             seL4_NilData,              /* cspace_root_data */
                             seL4_CapInitThreadVSpace,  /* vspace_root */
                             seL4_NilData,              /* vspace_root_data */
                             0,                         /* ipc_buffer */
                             seL4_CapNull);             /* ipc_buffer_frame */
    if (err != seL4_NoError) {
        printf("ERROR: Failed to configure server TCB: %d\n", err);
        return 1;
    }

    /* 6. Configure client TCB */
    err = seL4_TCB_Configure(SLOT_CLIENT_TCB,
                             seL4_CapNull,
                             seL4_CapInitThreadCNode,
                             seL4_NilData,
                             seL4_CapInitThreadVSpace,
                             seL4_NilData,
                             0,
                             seL4_CapNull);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to configure client TCB: %d\n", err);
        return 1;
    }
    printf("Configured both TCBs\n");

    /* 7. Set priorities - server higher than client */
    err = seL4_TCB_SetPriority(SLOT_SERVER_TCB, seL4_CapInitThreadTCB, 200);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to set server priority: %d\n", err);
        return 1;
    }

    err = seL4_TCB_SetPriority(SLOT_CLIENT_TCB, seL4_CapInitThreadTCB, 150);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to set client priority: %d\n", err);
        return 1;
    }
    printf("Set priorities (server=200, client=150)\n");

    /* 8. Write registers to set entry points and stacks */
    seL4_UserContext regs = {0};

    /* Server thread */
    regs.rip = (seL4_Word)echo_server_main;
    regs.rsp = (seL4_Word)(server_stack + STACK_SIZE);
    regs.rflags = 0x202;  /* Interrupts enabled */
    err = seL4_TCB_WriteRegisters(SLOT_SERVER_TCB,
                                  0,     /* don't resume yet */
                                  0,     /* arch_flags */
                                  sizeof(regs) / sizeof(seL4_Word),
                                  &regs);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to write server registers: %d\n", err);
        return 1;
    }

    /* Client thread */
    memset(&regs, 0, sizeof(regs));
    regs.rip = (seL4_Word)echo_client_main;
    regs.rsp = (seL4_Word)(client_stack + STACK_SIZE);
    regs.rflags = 0x202;
    err = seL4_TCB_WriteRegisters(SLOT_CLIENT_TCB,
                                  0,
                                  0,
                                  sizeof(regs) / sizeof(seL4_Word),
                                  &regs);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to write client registers: %d\n", err);
        return 1;
    }
    printf("Set entry points and stacks\n");

    /* 9. Resume both threads */
    printf("Starting server thread...\n");
    err = seL4_TCB_Resume(SLOT_SERVER_TCB);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to resume server: %d\n", err);
        return 1;
    }

    printf("Starting client thread...\n");
    err = seL4_TCB_Resume(SLOT_CLIENT_TCB);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to resume client: %d\n", err);
        return 1;
    }

    printf("Rootserver: Both threads started, yielding...\n");

    /* 10. Lower rootserver's priority so child threads can run */
    err = seL4_TCB_SetPriority(seL4_CapInitThreadTCB, seL4_CapInitThreadTCB, 100);
    if (err != seL4_NoError) {
        printf("ERROR: Failed to lower rootserver priority: %d\n", err);
    }

    /* Rootserver yields - server and client will run */
    while (1) {
        seL4_Yield();
    }

    return 0;
}
