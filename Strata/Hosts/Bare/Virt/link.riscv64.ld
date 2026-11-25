/* The image's memory layout on QEMU's `virt` machine, riscv64 (plan 0.140):
 * RAM starts at 0x8000_0000; `-bios none -kernel` loads the image there and
 * jumps to 0x8000_0000 itself, so the Host's `enter` (`_start`, in
 * `.text.start`) comes first. */
OUTPUT_ARCH(riscv)
ENTRY(_start)

SECTIONS
{
  . = 0x80000000;
  .text   : { KEEP(*(.text.start)) *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data   : { *(.data .data.* .sdata .sdata.*) }
  .bss    : { *(.bss .bss.* .sbss .sbss.* COMMON) }
}
