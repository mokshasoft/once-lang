# Bare Metal Compilation

## No Runtime Required

Once compiles to bare metal without requiring:

- Garbage collector
- Runtime system
- Operating system
- Dynamic memory allocator

This is possible because Once programs are compositions of simple operations that map directly to machine instructions.

## Why Once Works on Bare Metal

### Direct Mapping to Hardware

| Once Construct | Hardware Operation |
|----------------|-------------------|
| `compose f g` | Sequential instructions |
| `pair f g` | Compute both, store in registers/stack |
| `fst` / `snd` | Register/memory access |
| `case f g` | Conditional branch |
| `id` | No operation |

### No Hidden Costs

Traditional functional languages require:
- Heap allocation for closures
- Garbage collection
- Thunk evaluation (lazy languages)
- Runtime type information

Once avoids all of these:
- Closures compile to static code
- QTT tracks ownership, eliminating GC
- Strict evaluation, no thunks
- Types erased at compile time

## Memory Model

### Stack-Based Execution

Categorical composition naturally maps to stack operations:

```
-- Once source
processInput : Input -> Output
processInput = compose format (compose validate parse)

-- Compiles to (pseudocode)
processInput:
  call parse      ; result on stack
  call validate   ; consumes parse result, produces new result
  call format     ; consumes validate result, produces final output
  ret
```

### Product Layout

Products become contiguous memory:

```
-- Once type
Point : Int * Int

-- Memory layout
offset 0: first Int (8 bytes)
offset 8: second Int (8 bytes)
total: 16 bytes
```

### Sum Layout

Sums use tagged unions:

```
-- Once type
Result A E = A + E

-- Memory layout
offset 0: tag (1 byte, 0=success, 1=error)
offset 8: payload (max of A size, E size)
```

## QTT Enables No-GC Execution

Quantitative Type Theory tracks resource usage:

| Quantity | Meaning | Memory Impact |
|----------|---------|---------------|
| `0` | Compile-time only | No runtime storage |
| `1` | Used exactly once | Stack allocation, no GC |
| `ω` | Used any number | May need reference counting |

Linear code (`^1`) guarantees:
- Every allocation has exactly one consumer
- No dangling references
- No memory leaks
- Predictable stack usage

```
-- Linear function: buffer consumed exactly once
processBuffer : Buffer^1 -> Result^1
```

## Target Architectures

### ARM Cortex-M

Suitable for microcontrollers:

```
-- GPIO example
blink : Pin -> IO Unit
blink pin =
  bind (gpioWrite pin High) (\_ ->
  bind (delay 500) (\_ ->
  bind (gpioWrite pin Low) (\_ ->
  delay 500)))
```

Compiles to tight loop with direct register writes.

### RISC-V

Clean ISA makes code generation straightforward:

```
-- Product access
fst pair:
  ld a0, 0(a0)    ; load first element
  ret

snd pair:
  ld a0, 8(a0)    ; load second element
  ret
```

### x86-64

Standard calling conventions apply:

```
-- Function composition
compose_f_g:
  call g          ; result in rax
  mov rdi, rax    ; pass to f
  call f
  ret
```

## Embedded Systems Example

### LED Controller

```
-- Types
type Pin = Int
type Level = High + Low

-- Primitives (from bare-metal interpretation)
primitive gpioSetDirection : Pin -> Direction -> IO Unit
primitive gpioWrite : Pin -> Level -> IO Unit
primitive delayMs : Int -> IO Unit

-- Application
ledBlink : Pin -> IO Unit
ledBlink pin =
  bind (gpioSetDirection pin Output) (\_ ->
    loop (\_ ->
      bind (gpioWrite pin High) (\_ ->
      bind (delayMs 500) (\_ ->
      bind (gpioWrite pin Low) (\_ ->
      delayMs 500)))))
```

### Compiled Output

No OS dependencies. Links directly against:
- Startup code (vector table, stack setup)
- Primitive implementations (register writes)

Total binary size: typically under 10KB.

## Comparison with Alternatives

| Language | Runtime Needed | GC | Bare Metal Support |
|----------|---------------|----|--------------------|
| C | No | No | Native |
| Rust | Minimal | No | Excellent |
| Go | Yes | Yes | Limited |
| Haskell | Yes (RTS) | Yes | Very difficult |
| Once | No | No | Native |

Once achieves C-like bare metal support with stronger type guarantees.

## Constraints

### Stack Depth

Deep recursion may exceed available stack. Solutions:
- Tail call optimization (implemented)
- Convert to iteration during compilation
- Static stack analysis

### Code Size

Aggressive inlining increases code size. The compiler balances:
- Inline small functions (< threshold)
- Keep larger functions as calls
- User-controllable via pragmas

### Floating Point

Depends on target:
- Hardware FPU: native operations
- Soft float: library calls
- Integer only: use fixed-point types

## Getting Started

### Compile for Bare Metal

```bash
once build program.once --target=arm-none-eabi --interp=bare-metal/stm32
```

### Link with Startup Code

```bash
arm-none-eabi-gcc -nostdlib -T linker.ld startup.o program.o -o firmware.elf
```

### Flash to Device

```bash
st-flash write firmware.bin 0x8000000
```

## Summary

Once's design makes bare metal compilation natural:

| Property | Benefit |
|----------|---------|
| Categorical foundations | Direct hardware mapping |
| QTT linearity | No garbage collector needed |
| Explicit IO | Clear hardware interactions |
| No runtime | Minimal binary size |
| Type safety | Catch errors at compile time |

The combination of mathematical rigor and practical minimalism makes Once suitable for safety-critical embedded systems where both correctness and resource constraints matter.
