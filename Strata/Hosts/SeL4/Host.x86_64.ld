/* The seL4 Host's entry (Host.x86_64): the kernel starts the root task here,
   with no stack. Passed to ld as an implicit linker script; ld's default
   layout is unchanged. */
ENTRY(once_sel4_enter)
