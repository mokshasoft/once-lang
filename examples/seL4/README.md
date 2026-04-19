# seL4 Echo Server Example

This example demonstrates running Once code on the seL4 microkernel.

## Overview

The example consists of three Once programs:

1. **Rootserver** (`Rootserver/Rootserver.once`) - The initial user-space
   thread that owns all capabilities and distributes them to child processes.

2. **EchoServer** (`EchoServer/EchoServer.once`) - A server that receives
   IPC messages and echoes them back.

3. **EchoClient** (`EchoServer/echo-client.once`) - A client that sends
   test messages and verifies the echoed responses.

## Why Once for seL4?

seL4 is formally verified, but user-space code running on seL4 typically isn't.
The rootserver is particularly security-critical because it:

- Owns all initial capabilities
- Decides which capabilities to give to which processes
- Controls the entire system's access policy

By writing the rootserver in Once, we can formally verify this critical code,
extending the verification boundary from the kernel into user space.

## Architecture Support

The seL4 interpretation files support three architectures:

| Architecture | Platform | QEMU Command |
|--------------|----------|--------------|
| ARM64 | qemu-arm-virt | `qemu-system-aarch64 -machine virt -cpu cortex-a53` |
| x86_64 | pc99 | `qemu-system-x86_64 -machine q35` |
| RISC-V64 | qemu-riscv-virt | `qemu-system-riscv64 -machine virt` |

## Building

### Prerequisites

Enter the appropriate development shell:

```bash
nix develop .#arm64    # For ARM64 development
nix develop .#riscv64  # For RISC-V development
nix develop .#x86-64   # For x86-64 development
nix develop .#full     # All cross-compilers + QEMU
```

Each shell provides:
- The Once compiler (via stack)
- Architecture-specific cross-compiler
- QEMU for simulation

### Build Steps

1. Build the seL4 kernel:
   ```bash
   nix build .#seL4-arm64   # For ARM64
   nix build .#seL4-x86_64  # For x86_64
   nix build .#seL4-riscv64 # For RISC-V
   ```

2. Compile Once programs:
   ```bash
   # From the once-lang root directory
   cd compiler
   cabal build

   # Build rootserver
   cabal run once -- build \
     --exe \
     --interp ../Strata/Interpretations/seL4 \
     ../examples/seL4/Rootserver/Rootserver.once \
     -o ../examples/seL4/build/rootserver

   # Build echo server
   cabal run once -- build \
     --exe \
     --interp ../Strata/Interpretations/seL4 \
     ../examples/seL4/EchoServer/EchoServer.once \
     -o ../examples/seL4/build/echo-server

   # Build echo client
   cabal run once -- build \
     --exe \
     --interp ../Strata/Interpretations/seL4 \
     ../examples/seL4/EchoServer/echo-client.once \
     -o ../examples/seL4/build/echo-client
   ```

3. Link with cross-compiler:
   ```bash
   aarch64-none-elf-gcc -nostdlib -ffreestanding \
     -o build/rootserver.elf build/rootserver.c
   ```

### Native Assembly Generation

The Once compiler can generate native assembly instead of C for tighter
integration and smaller code size. Use `--target` to select the architecture:

```bash
# Generate x86-64 assembly (library mode)
cabal run once -- build \
  --target x86_64 \
  --strata ../Strata \
  -I:x86_64 I.SeL4.IPC \
  ../examples/seL4/EchoServer/echo-client-simple.once \
  -o ../examples/seL4/build/echo-client

# This generates echo-client.s (assembly file)
```

Supported targets:
- `x86_64` - x86-64 assembly (AT&T syntax for GNU assembler)
- `arm64` - ARM64/AArch64 assembly
- `riscv64` - RISC-V 64-bit assembly
- `c` - C code (default, most complete)

The native targets use interpretation files with matching extensions:
- `-I:x86_64 I.SeL4.IPC` uses `Strata/Interpretations/SeL4/IPC.x86_64`
- `-I:C I.SeL4.IPC` uses `Strata/Interpretations/SeL4/IPC.c`

**Note:** The native assembly generators support let-bindings, integer
constants, and function calls. For full language support (strings, complex
closures), use the C backend.

## Running in QEMU

Use the simulation scripts:

```bash
./scripts/simulate-arm.sh build/arm64/kernel.elf
./scripts/simulate-x86.sh build/x86_64/kernel.elf
./scripts/simulate-riscv.sh build/riscv64/kernel.elf
```

Or use nix run:

```bash
nix run .#simulate-arm -- path/to/kernel.elf
```

Press `Ctrl-A X` to exit QEMU.

## seL4 Primitives

The Once seL4 interpretation provides these primitives:

### IPC (`I.seL4.IPC`)
- `seL4_Send` - Send message (blocking)
- `seL4_NBSend` - Send message (non-blocking)
- `seL4_Recv` - Receive message
- `seL4_NBRecv` - Receive (non-blocking)
- `seL4_Call` - Send and wait for reply
- `seL4_Reply` - Reply to caller
- `seL4_ReplyRecv` - Reply and wait for next
- `seL4_Yield` - Yield CPU

### Notifications (`I.seL4.Notification`)
- `seL4_Signal` - Signal a notification
- `seL4_Wait` - Wait on notification
- `seL4_Poll` - Poll notification (non-blocking)

### Untyped Memory (`I.seL4.Untyped`)
- `seL4_Untyped_Retype` - Create kernel objects

### Capabilities (`I.seL4.CNode`)
- `seL4_CNode_Copy` - Copy capability
- `seL4_CNode_Mint` - Copy with badge
- `seL4_CNode_Move` - Move capability
- `seL4_CNode_Delete` - Delete capability
- `seL4_CNode_Revoke` - Revoke derived caps

### Thread Control (`I.seL4.TCB`)
- `seL4_TCB_Configure` - Configure address spaces
- `seL4_TCB_SetPriority` - Set priority
- `seL4_TCB_Resume` - Start/resume thread
- `seL4_TCB_Suspend` - Suspend thread
- `seL4_TCB_WriteRegisters` - Set registers
- `seL4_TCB_ReadRegisters` - Get registers

### Boot Info (`I.seL4.BootInfo`)
- `getBootInfo` - Get BootInfo pointer
- `bootinfo_untypedCount` - Number of untyped regions
- `bootinfo_untypedStart` - First untyped cap slot
- `bootinfo_getUntyped` - Get untyped descriptor

## Verification Status

| Component | Verified |
|-----------|----------|
| seL4 kernel | Yes (by seL4 project) |
| Once type system | Yes (in Agda) |
| Rootserver logic | Yes (via Once types) |
| IPC assembly glue | No (trusted, matches seL4 API) |

The assembly glue code in the interpretation files is equivalent to the
stubs in seL4's `libsel4` library - thin wrappers that call the kernel
using the documented syscall ABI.

## Directory Structure

```
examples/seL4/
├── flake.nix           # Nix build with seL4 + QEMU
├── README.md           # This file
├── Rootserver/
│   └── Rootserver.once # Security-critical cap distribution
├── EchoServer/
│   ├── EchoServer.once # Echo server
│   └── echo-client.once # Echo client
├── config/             # CMake toolchain files
└── scripts/
    ├── simulate-arm.sh
    ├── simulate-x86.sh
    └── simulate-riscv.sh
```

## Further Reading

- [seL4 Reference Manual](https://sel4.systems/Info/Docs/seL4-manual-latest.pdf)
- [Once Language Design](../../docs/design/overview.md)
- [Bare Metal Support](../../docs/design/bare-metal.md)
