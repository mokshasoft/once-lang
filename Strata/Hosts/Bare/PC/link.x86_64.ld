/* The image's memory layout on QEMU's `pc` machine, x86_64 (plan 0.140, O2):
 * QEMU's `-kernel` loads a Multiboot kernel only from a 32-bit ELF, and enters
 * it in 32-bit protected mode. So the image is linked from the 64-bit objects
 * into an ELF32 container (every address is below 4 GiB, so nothing is lost),
 * and the Host's `_start` is 32-bit code that enters long mode. The Multiboot
 * header must lie in the image's first 8 KiB, so it comes first; the image
 * starts at 1 MiB, above the BIOS area. */
OUTPUT_FORMAT(elf32-i386)
OUTPUT_ARCH(i386:x86-64)
ENTRY(_start)

SECTIONS
{
  . = 0x100000;
  .text   : { KEEP(*(.multiboot)) KEEP(*(.text.start)) *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data   : { *(.data .data.*) }
  .bss    : { *(.bss .bss.* COMMON) }
}
