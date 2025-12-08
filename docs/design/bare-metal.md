# Once on Bare Metal

## Why Once is Bare-Metal Ready

Once's categorical foundation makes it exceptionally suitable for bare-metal compilation - no OS, no runtime system, no garbage collector required.

### What Once Doesn't Need

| Typical Requirement | Why Once Doesn't Need It |
|---------------------|------------------------|
| **Garbage Collector** | Composition is stack-based; no implicit allocation |
| **Runtime System** | No green threads, no thunks, no lazy evaluation |
| **OS System Calls** | Pure computation is self-contained; effects explicit |
| **Dynamic Memory** | Can be entirely stack-allocated or arena-based |
| **Exception Handling** | Errors are values (coproducts), not control flow |

### What's Left After Compilation

```
Source:  compose g f x
After:   g(f(x))        -- just function calls
Machine: call, call, ret
```

The categorical combinators reduce to:
- **Function calls** (composition)
- **Stack operations** (products/pairs)
- **Branches** (sums/case)
- **Returns** (identity)

That's it. No malloc, no GC, no runtime.

## Comparison with Other Languages

| Language | Bare-Metal Viable? | Why/Why Not |
|----------|-------------------|-------------|
| **C** | Yes | Manual memory, explicit everything |
| **Rust** | Yes | Ownership system, no GC |
| **Haskell/GHC** | Difficult | Requires RTS, GC, lazy evaluation |
| **Once** | Yes | Pure composition, effects explicit, no hidden allocation |
| **Forth** | Yes | Stack-based, minimal |

Once is closer to Forth than to Haskell in this regard.

## Memory Model

### Stack-Based Execution

```
-- Categorical composition is naturally stack-based

compose h (compose g f)
-- Compiles to:
--   push arg
--   call f
--   call g  (uses result of f)
--   call h  (uses result of g)
--   ret

pair x y  -- product
-- Compiles to:
--   push y
--   push x
--   (both on stack as a pair)

case f g  -- sum/case
-- Compiles to:
--   branch on tag
--   jmp left_handler / jmp right_handler
```

### No Hidden Allocation

In typical functional languages:
```
map f xs  -- allocates new list cells, needs GC
```

In Once:
```
fmap f  -- just function composition
-- The structure is in the types, not allocated at runtime
```

### Effect-Based Resource Management

Effects are **type-level annotations**, not runtime constructs:

```
type Machine item = State (List item) * Halts
```

A bare-metal compiler would:
1. See `State` → allocate fixed space for state
2. See `Halts` → generate early-return paths
3. See `List` → use a fixed-size array or stack region

## Bare-Metal Compilation Strategy

### 1. Effect Analysis

```
analyze : Program -> Effects
-- Extract which effects are used
-- Determines memory layout and control flow
```

### 2. Memory Layout

```
layout : Effects -> MemoryMap
-- State effects → static allocation
-- List/Tree → stack or arena
-- No effect → registers only
```

### 3. Code Generation

```
codegen : IR -> Assembly
-- Composition → call/jmp
-- Products → stack push
-- Sums → conditional branch
-- Fmap → inline or loop
```

### Example: Stack Machine on Bare Metal

A stack machine program compiles to:

```asm
; Machine state in registers/fixed memory
; r0 = stack pointer
; r1 = program counter
; [0x1000-0x1100] = value stack

load:
    ; push immediate to stack
    mov [r0], arg
    add r0, 8
    ret

eval:
    ; pop two, apply binop, push result
    sub r0, 8
    mov r2, [r0]      ; first operand
    sub r0, 8
    mov r3, [r0]      ; second operand
    call binop        ; r2, r3 -> r4
    mov [r0], r4
    add r0, 8
    ret

main:
    ; dispatch loop
.loop:
    mov r1, [pc]
    add pc, 8
    cmp r1, IMMEDIATE
    je load
    cmp r1, OPERATION
    je eval
    jmp .done
.done:
    ret
```

No OS. No malloc. No GC. Just registers, stack, and branches.

## Target Platforms

| Platform | Feasibility | Notes |
|----------|-------------|-------|
| **x86/x64** | Excellent | Standard calling conventions |
| **ARM** | Excellent | Good register set for stack ops |
| **RISC-V** | Excellent | Clean ISA, easy codegen |
| **WebAssembly** | Excellent | Stack-based, perfect match |
| **Microcontrollers** | Good | May need to limit recursion depth |
| **FPGA/Hardware** | Interesting | Categorical circuits |

## The Forth Connection

The categorical style naturally maps to stack-based computation:

```
Forth:          : double dup + ;
Once:           double = compose add diagonal
Categorical:    double = (+) ∘ Δ   -- diagonal then add
Assembly:       push [sp], add [sp], [sp-8], pop
```

All are equivalent representations of the same computation.

## Linearity and Memory

Once uses **Quantitative Type Theory (QTT)** to track resource usage. When code has quantity `1` (linear), memory management becomes trivial:

- Each value used exactly once
- No copies, no GC
- Clear ownership transfer
- Stack allocation only

The compiler infers quantities and can report them:

```
> once analyze myFunction

myFunction : Buffer^1 -> Result^1
  Quantity: linear (1)
  -> No GC needed, stack allocation only
```

Linearity is **enforced by the type system**. If you annotate a function as linear and it isn't, compilation fails. See [Memory](memory.md) for details on QTT.

## Conclusion

Once is **ideal for bare-metal** because:

1. **No runtime** - Pure composition doesn't need one
2. **No GC** - Linearity eliminates hidden allocation
3. **Explicit effects** - Compiler knows exactly what's needed
4. **Stack-based** - Natural fit for hardware execution model
5. **Mathematical semantics** - Easy to verify correctness

The real target for Once is firmware, embedded systems, or even hardware synthesis - anywhere you need correctness without runtime overhead.
