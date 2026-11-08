# seL4 Echo Server Example

Once programs running on the seL4 microkernel (x86_64, x86_32 and riscv64, under QEMU): a root task, an echo server and
a client, all written in Once. The client calls the server over an seL4 endpoint with the Ints 65 to
90 and prints each answer; the server answers with what it received. No C runs in this path:
the kernel starts the root task, and everything after that is Once code and the thin per-arch
assembly of the seL4 Interpretations and Host ([plan 0.127](../../plans/0.127-sel4-runs-once.md)).

## Run it

```sh
nix build .#echo-test-x86_64 -L      # build compiler, kernel and image; boot under QEMU; check the output
nix build .#exhausted-test-x86_64 -L # a root task that allocates without bound faults
nix build .#monitored-test-x86_64 -L # a monitor receives a program's out-of-memory fault
nix build .#caps-test-x86_64 -L      # a root task runs every CNode and Notification operation
nix build .#numbers-check-x86_64 -L  # check every seL4 number in the Strata against the kernel
nix build .#all -L                   # all five, on every architecture
nix run .#simulate-x86_64            # boot the echo interactively (Ctrl-A X quits QEMU)
```

Each name exists for `x86_64`, `x86_32` and `riscv64`.

Everything is built by Nix: the Once compiler from this repository, the pinned seL4 kernel, and the
image. `echo-test` passes when the console shows

```
0000000
Once: returned
ABCDEFGHIJKLMNOPQRSTUVWXYZ
Once: returned
```

`0000000` is the root task's seven seL4 invocations, each printing `'0' + its error`; the alphabet is
what the client printed from the server's answers; `Once: returned` is the seL4 Host's `leave`, once
for the root task and once for the client. The server never returns: it waits for the next call.

## The programs

The image holds three Once programs (`Echo/`), each with its own `main`, its own run, stack and heap:

| Program | File | What it does |
|---|---|---|
| 0, the root task | `Root.once` | finds untyped RAM in the bootinfo; makes two TCBs and an endpoint; configures both threads with its own CSpace and VSpace; starts program 1 and program 2 on them with the endpoint's slot |
| 1, the server | `Server.once` | forever: `seL4_Recv` on the endpoint, `seL4_Reply` with the first message word |
| 2, the client | `Client.once` | for 65 to 90: `seL4_Call` the server, print the answer with `seL4_DebugPutChar` |

`link-image.sh` builds each program alone and links them into one ELF: program 0 keeps `once_main`
(the compiler's portable entry); program n's `once_main` (its only global symbol) is renamed
`once_program_<n>`, which the seL4 Host's program table names. `I.SeL4.Program.start` starts program
n on a thread at the Host's `once_sel4_program_enter`, with the stack pointer at the top of the
region the Host keeps for it; that points the heap at the region's bottom and jumps to the program.

Each program's region is 1 MiB, its cells growing up from the bottom and its stack down from the
top (plan 0.123 C.5). When the two would meet, a room check in the program calls the Host's
`once_exhausted`, and the thread faults, the usual way for an seL4 thread that cannot go on: the
kernel sends a fault message to the endpoint named in the thread's TCB, and the thread waits for its
supervisor. `Exhausted/Monitor.once` is such a supervisor (`monitored-test`). A thread with no fault
endpoint, like the root task, is reported on the kernel's console and stopped (`exhausted-test`).

The programs share the root task's address space and CSpace for now; giving each its own CNode
(and later VSpace) is the step towards isolation.

## The pieces

- `Strata/Hosts/SeL4/Host.<arch>` — the seL4 Host: the root task's entry `_start` (its region's
  stack and heap, the bootinfo pointer saved, then the compiler's `once_main`), the program table,
  regions and entry, `leave` (print a line, suspend the thread) and `exhausted` (fault).
- `Strata/Interpretations/SeL4/` — `BootInfo`, `Untyped`, `TCB`, `CNode`, `IPC`, `Notification`,
  `Debug`, `Program`, one file per architecture. The Host holds their shared routines (reading a
  tuple argument, building a tuple answer, an object invocation).
- `check-numbers.sh` — every seL4 number (syscall numbers, invocation message infos, object types,
  struct offsets, capability slots, rights bits) sits in a `seL4 numbers` block of its file, named
  by the kernel's name or with the C expression it must equal; the check compiles them against the
  pinned kernel's own headers and fails on any difference. (It found `seL4_SlotBits` and the read
  and write rights wrong, besides the syscall numbers.)
- `flake.nix` — one row per architecture (its kernel, its linking tools, how QEMU boots an image);
  the examples, the checks and `simulate` are made for every row.
- `riscv64-boot/` — on riscv64 the kernel and the root task boot together inside seL4's elfloader,
  which QEMU's OpenSBI starts; this CMake project builds the elfloader around a Once image.

## Not yet

- Reclaiming the heap: nothing does yet (plan 0.146); a program that outruns its 1 MiB region
  faults.
- Isolation between the programs (own CNode, own VSpace) and IPC buffers for started programs
  ([plan 0.148](../../plans/0.148-sel4-isolation-and-ipc-buffers.md)). Until they have a buffer, they
  send and receive only the register words: four on x86_64 and riscv64, two on x86_32. The root task
  has a buffer and sends all four words of `seL4_Send` and `seL4_Call` on every architecture.
