# Claude Code Guidelines for Once Language

## IMPORTANT: Always Run Test Programs

When creating or modifying example programs, ALWAYS:
1. Build them with the Once compiler
2. Compile the generated C with gcc
3. Run the executable to verify it works

Do not commit examples without verifying they compile and run.

## Build Directory

Use `.build/` for compiler output (generated C files, executables):

```bash
# From compiler/ directory:
stack exec -- once build --exe --interp ../Strata/Interpretations/Linux ../examples/hello.once -o ../.build/hello

# Compile with gcc:
gcc -o ../.build/hello ../.build/hello.c

# Run:
../.build/hello
```

Do NOT use `/tmp/` for build output - use `.build/` instead.

## Running the Compiler

The Once compiler is in `compiler/`. To build and run:

```bash
cd compiler
stack build                    # Build the compiler
stack test                     # Run tests
stack exec -- once build ...   # Run the compiler
```

## Interpretation Files

Interpretation files are in `Strata/Interpretations/Linux/`:
- `syscalls.once` / `syscalls.c` - Raw Linux syscalls
- `File.once` / `File.c` - File I/O convenience functions
- `memory.once` / `memory.c` - MallocLike interface (alloc/free/realloc)

### Type Definition Guards

All `.c` files must use include guards for types since the compiler concatenates them:

```c
#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
#endif
```

## Agda Formal Proofs

The formal proofs are in `formal/`. Run from the `formal/` directory:

```bash
cd formal
make           # Type-check all proofs
make laws      # Type-check categorical laws only
make surface   # Type-check surface syntax elaboration only
make x86       # Type-check x86-64 backend proofs
make clean     # Remove Agda build artifacts
```

The `make` targets automatically handle the Nix shell environment and library paths.

## Existing Test Failures

There are 4 pre-existing test failures related to OnceString/OnceBuffer type ordering in the C backend codegen. These are known issues not related to current work.
