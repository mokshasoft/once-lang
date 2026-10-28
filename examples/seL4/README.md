# seL4 Echo Server Example

Once programs running on the seL4 microkernel (x86_64, under QEMU): a root task, an echo server and
a client, all written in Once. The client calls the server over an seL4 endpoint with the Ints 65 to
90 and prints each answer; the server answers with what it received. No C runs in this path:
the kernel starts the root task, and everything after that is Once code and the thin per-arch
assembly of the seL4 Interpretations and Host ([plan 0.127](../../plans/0.127-sel4-runs-once.md)).

## Run it

```sh
nix build .#echo-test -L     # build compiler, kernel and image; boot under QEMU; check the output
nix build .#numbers-check -L # check every seL4 number in the Strata against the kernel
nix flake check              # both
nix run .#simulate           # boot it interactively (Ctrl-A X quits QEMU)
```

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

`link-image.sh` builds each program alone and links them into one ELF: program 0 keeps `_start`;
program n's `_start` (its only global symbol) is renamed `once_program_<n>`, which the seL4 Host's
program table names. `I.SeL4.Program.start` starts program n on a thread at that address, on the
stack the Host keeps for it.

The programs share the root task's address space and CSpace for now; giving each its own CNode
(and later VSpace) is the step towards isolation.

## The pieces

- `Strata/Hosts/SeL4/Host.x86_64` — the seL4 Host: the root task's entry (a stack, the bootinfo
  pointer saved, then the compiler's `_start`), the program table and stacks, and `leave` (print a
  line, suspend the thread). `Host.x86_64.ld` names the entry for the link.
- `Strata/Interpretations/SeL4/` — `BootInfo`, `Untyped`, `TCB`, `CNode`, `IPC`, `Notification`,
  `Debug`, `Program`, x86_64 only. The Host holds their shared routines (reading a tuple argument,
  building a tuple answer, an object invocation).
- `check-numbers.sh` — every seL4 number (syscall numbers, invocation message infos, object types,
  struct offsets, capability slots, rights bits) sits in a `seL4 numbers` block of its file, named
  by the kernel's name or with the C expression it must equal; the check compiles them against the
  pinned kernel's own headers and fails on any difference. (It found `seL4_SlotBits` and the read
  and write rights wrong, besides the syscall numbers.)
- `flake.nix` — the kernel (`seL4-kernel-x86_64`: pc99, debug, printing, seL4's own simulation
  settings), the image (`echo-image`), the checks (`echo-test`, `numbers-check`) and `simulate`.

## Not yet

- Other architectures: riscv64 and x86_32 (plan 0.127 C); arm64 once there is an ARM64 backend.
- `CNode` and `Notification` are number-checked but not yet run: `Caps/Root.once` tests them, but a
  root task alone runs out of its 64 KiB heap into its stack before it starts (nothing reclaims the
  heap yet, and running out is not yet detected: plan 0.123). In the echo image the root task's
  heap overflows into the server's and client's unused heaps, which is why that test passes.
- Isolation between the programs (own CNode, own VSpace).
- Message lengths beyond the four register words (needs an IPC buffer per thread).
