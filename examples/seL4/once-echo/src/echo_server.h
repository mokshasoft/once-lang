/*
 * Once Echo - Header declarations
 *
 * Entry points for the echo server and client threads.
 */

#pragma once

/* Echo server entry point - receives messages and echoes them back */
void echo_server_main(void);

/* Echo client entry point - sends messages and verifies responses */
void echo_client_main(void);
