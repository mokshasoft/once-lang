# Foreign Function Interface in Once

## Two Directions

Once's FFI works in both directions:

| Direction | Meaning | Use Case |
|-----------|---------|----------|
| **Calling out** | Once code calls external functions | OS APIs, hardware, existing C libraries |
| **Calling in** | External code calls Once functions | Once as a library for other languages |

Both are first-class concerns. Once is designed to be embedded, not just to be a standalone executable.

## Calling Out: Primitive Declarations

External functions are declared as **primitives** in the Interpretation layer:

```
-- System calls
primitive sys_read  : FileDescriptor * Buffer * Size -> External SSize
primitive sys_write : FileDescriptor * Buffer * Size -> External SSize
primitive sys_open  : Path * Flags -> External (FileDescriptor + Error)

-- Hardware (bare metal)
primitive gpio_read  : Pin -> External Bit
primitive gpio_write : Pin * Bit -> External Unit

-- Existing C libraries
primitive strlen : CString -> Size
primitive memcpy : Dest * Src * Size -> Dest
```

### Foreign Type Mapping

Once types map to C types:

| Once Type | C Type | Notes |
|-----------|--------|-------|
| `Unit` | `void` | No return value |
| `Byte` | `uint8_t` | Single byte |
| `Int` | `int64_t` | Default integer |
| `A * B` | `struct { A fst; B snd; }` | Product |
| `A + B` | Tagged union | Coproduct |
| `A -> B` | `B (*)(A)` | Function pointer |

### Opaque Types

For types that shouldn't be inspected:

```
-- Opaque: no internal structure visible to Once
opaque FileHandle
opaque Socket
opaque CString

-- Primitives work with opaque types
primitive fopen  : Path * Mode -> External (FileHandle + Error)
primitive fclose : FileHandle -> External Unit
```

Opaque types are:
- Created only by primitives
- Consumed only by primitives
- Cannot be pattern-matched or destructured
- Passed through Once code unchanged

## Calling In: Exports

Once functions can be exported with C calling convention:

```
-- Mark a function for export
export parseJson : CString * Size -> JsonResult

-- Implementation is pure Once
parseJson input len =
  compose validate (compose parse (fromCString input len))
```

### What Gets Generated

For each export, the Once compiler generates:

```c
// C header
JsonResult once_parseJson(const char* input, size_t len);

// Implementation calls into compiled Once code
JsonResult once_parseJson(const char* input, size_t len) {
    return _once_internal_parseJson(input, len);
}
```

### Callback Support

Once can provide callbacks to foreign code:

```
-- A callback type
type Callback = Int -> External Unit

-- Export a function that returns a callback
export makeHandler : Config -> Callback

-- Foreign code can call:
--   Callback cb = once_makeHandler(config);
--   cb(42);  // invokes Once code
```

## Memory Management at the Boundary

### The Problem

Once doesn't have garbage collection. External code might expect:
- Allocated buffers
- Caller-frees semantics
- Reference counting

### The Solution: Explicit Protocols

```
-- Allocation primitives
primitive malloc : Size -> External (Ptr + Null)
primitive free   : Ptr -> External Unit

-- Once code that allocates for foreign consumption
export createBuffer : Size -> Ptr
createBuffer size =
  case malloc size of
    inl ptr  -> ptr
    inr null -> initial  -- absurd, or handle error

-- Caller is responsible for freeing
-- Document this in the export
```

For complex data:

```
-- Serialize to foreign-friendly format
export serializeResult : Result -> CString * Size

-- Or use caller-provided buffer
export serializeInto : Result * Buffer * Size -> Size + Error
```

### Linear Discipline at Boundaries

Once uses **Quantitative Type Theory (QTT)** to track resource usage. If code has quantity `1` (linear), memory management is straightforward:
- Each value used exactly once
- No hidden copies
- Clear ownership transfer

Linearity is **enforced by the type system**:

```
-- Type guarantees linearity
export processBuffer : Buffer^1 -> Result^1
-- Caller receives sole ownership, must use result exactly once
```

See [Memory](memory.md) for details on QTT.

## Platform Interpretation Layers

Different targets have different primitives:

### POSIX Interpretation

```
-- File operations
primitive open  : Path * Flags -> External (Fd + Errno)
primitive read  : Fd * Buf * Size -> External (SSize + Errno)
primitive write : Fd * Buf * Size -> External (SSize + Errno)
primitive close : Fd -> External (Unit + Errno)

-- Memory
primitive mmap : Addr * Size * Prot * Flags * Fd * Off -> External (Addr + Errno)
```

### Bare Metal Interpretation (e.g., BeagleBone)

```
-- GPIO
primitive gpio_direction : Pin * Direction -> External Unit
primitive gpio_write     : Pin * Level -> External Unit
primitive gpio_read      : Pin -> External Level

-- Memory-mapped IO
primitive mmio_read  : Address -> External Word
primitive mmio_write : Address * Word -> External Unit

-- Interrupts
primitive enable_interrupt  : IRQ * Handler -> External Unit
primitive disable_interrupt : IRQ -> External Unit
```

### WebAssembly Interpretation

```
-- Host imports
primitive console_log : CString * Size -> External Unit
primitive fetch       : Url -> External (Response + Error)

-- Memory (WASM linear memory)
primitive memory_grow : Pages -> External (PageIndex + Error)
```

## Example: Once Library Used from C

### Once Source

```
-- math.once

-- Pure function, no IO
export gcd : Int * Int -> Int
gcd (a, b) = case b of
  0 -> a
  _ -> gcd (b, mod a b)

-- Function that uses state internally but exports pure interface
export fibonacci : Int -> Int
fibonacci n = fst (iterate n step (0, 1))
  where step (a, b) = (b, a + b)
```

### Generated C Header

```c
// math.h - generated by Once compiler
#ifndef ONCE_MATH_H
#define ONCE_MATH_H

#include <stdint.h>

int64_t once_gcd(int64_t a, int64_t b);
int64_t once_fibonacci(int64_t n);

#endif
```

### Usage from C

```c
#include "math.h"
#include <stdio.h>

int main() {
    printf("gcd(48, 18) = %ld\n", once_gcd(48, 18));
    printf("fib(10) = %ld\n", once_fibonacci(10));
    return 0;
}
```

## Example: Wrapping a C Library

### C Library (existing)

```c
// zlib.h
int compress(Bytef *dest, uLongf *destLen,
             const Bytef *source, uLong sourceLen);
```

### Once Wrapper

```
-- zlib.once

opaque Bytef
opaque ULong

-- Primitive declaration
primitive c_compress : Bytef * ULong * Bytef * ULong -> External Int

-- Once-friendly wrapper
compress : Bytes -> External (Bytes + Error)
compress input =
  let inputLen = length input
      maxOutput = compressBound inputLen
  in case malloc maxOutput of
    inr null -> inr OutOfMemory
    inl dest ->
      case c_compress dest maxOutput (toPtr input) inputLen of
        0 -> inl (fromPtr dest actualLen)
        e -> inr (ZlibError e)
```

## Summary

| Aspect | Mechanism |
|--------|-----------|
| Calling out | `primitive` declarations |
| Calling in | `export` declarations |
| Opaque foreign types | `opaque` keyword |
| Type mapping | Direct correspondence to C |
| Memory | Explicit allocation primitives |
| Callbacks | Function types export as function pointers |
| Platform differences | Different Interpretation layers |

Once is designed to be a **library language** - not just for writing applications, but for writing libraries that any language can use. The natural transformation foundation means no runtime, no GC, just functions with C-compatible calling conventions.
