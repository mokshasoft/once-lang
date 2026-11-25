/* The image's memory layout on QEMU's `pc` machine, x86_32 (plan 0.140):
 * QEMU's `-kernel` loads a Multiboot ELF at its own physical addresses and
 * jumps to its entry in 32-bit protected mode. The Multiboot header must lie
 * in the image's first 8 KiB, so it comes first; the image starts at 1 MiB,
 * above the BIOS area. */
OUTPUT_FORMAT(elf32-i386)
OUTPUT_ARCH(i386)
ENTRY(_start)

SECTIONS
{
  . = 0x100000;
  .text   : { KEEP(*(.multiboot)) KEEP(*(.text.start)) *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data   : { *(.data .data.*) }
  .bss    : { *(.bss .bss.* COMMON) }
}
