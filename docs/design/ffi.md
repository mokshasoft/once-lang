# Foreign Function Interface

## Overview

Once provides bidirectional interoperability with other languages:

- **Import**: Call external functions from Once code
- **Export**: Make Once functions callable from other languages

This enables Once to integrate with existing codebases, use platform APIs, and serve as a library for other languages.

## Importing External Functions

External functions are declared with the `primitive` keyword in the Interpretations stratum:

```
primitive puts : String -> IO Unit
primitive getenv : String -> IO (String + Null)
```

### Type Correspondence

Once types map to C types (the common FFI target):

| Once | C |
|------|---|
| `Unit` | `void` (as return) |
| `Int` | `int64_t` |
| `Byte` | `uint8_t` |
| `Bool` | `int` (0/1) |
| `A * B` | `struct { A fst; B snd; }` |
| `A + B` | tagged union |
| `String` | `char*` + length |
| `A -> B` | function pointer |

### Opaque Types

For foreign types whose internals Once shouldn't access:

```
opaque FileHandle
opaque Socket
opaque Regex

primitive fopen : String -> String -> IO (FileHandle + Error)
primitive fclose : FileHandle -> IO Unit
```

Opaque types:
- Can only be created/consumed by primitives
- Pass through Once code unchanged
- Cannot be pattern matched

## Exporting Once Functions

Once functions become callable from C using `export`:

```
export factorial : Int -> Int
factorial n = case n of
  0 -> 1
  _ -> multiply n (factorial (subtract n 1))
```

### Generated Interface

The compiler produces a C header:

```c
// factorial.h
#pragma once
#include <stdint.h>

int64_t once_factorial(int64_t n);
```

And corresponding implementation that calls the compiled Once code.

### Export Conventions

Exported functions use the C ABI:
- No garbage collector
- No runtime required
- Predictable memory layout
- Standard calling conventions

## Memory at the Boundary

### Ownership Rules

Once doesn't manage memory for foreign code. At boundaries:

1. **Once allocates, caller frees**: Document this explicitly
2. **Caller allocates, Once uses**: Provide buffer + size
3. **Shared ownership**: Use reference counting primitives

### Buffer Patterns

```
-- Caller provides buffer
export renderJson : Json -> Buffer -> Size -> Size + Error

-- Once allocates (caller must free)
export encodeBase64 : Bytes -> IO (Buffer * Size)
```

### QTT at Boundaries

Linear types (`^1`) clarify ownership:

```
export processBuffer : Buffer^1 -> Result^1
-- Ownership transfers: caller gives up buffer, receives result
```

## Complete Example: JSON Library

### Once Source

```
-- json.once

type Json
  = JsonNull
  + JsonBool Bool
  + JsonNum Int
  + JsonStr String
  + JsonArr (List Json)
  + JsonObj (List (String * Json))

-- Pure parsing (Derived stratum)
parseJson : String -> Result Json ParseError
parseJson = ...

-- Export with C-friendly interface
export json_parse : CString -> Size -> JsonResult
json_parse str len =
  case parseJson (fromCString str len) of
    ok json -> JsonOk json
    err e   -> JsonErr (errorCode e)

export json_free : JsonHandle -> IO Unit
json_free = ...
```

### Generated Header

```c
// json.h
#pragma once

typedef struct JsonResult {
    int tag;  // 0 = ok, 1 = error
    union {
        void* json;    // opaque handle
        int error_code;
    } val;
} JsonResult;

JsonResult once_json_parse(const char* str, size_t len);
void once_json_free(void* json);
```

### Usage from C

```c
#include "json.h"
#include <stdio.h>

int main() {
    const char* input = "{\"name\": \"test\"}";
    JsonResult r = once_json_parse(input, strlen(input));

    if (r.tag == 0) {
        // Use json handle...
        once_json_free(r.val.json);
    } else {
        printf("Parse error: %d\n", r.val.error_code);
    }
    return 0;
}
```

## Platform-Specific Primitives

Different interpretation modules provide different primitives:

### Linux

```
primitive read  : Fd -> Buffer -> Size -> IO (Size + Errno)
primitive write : Fd -> Buffer -> Size -> IO (Size + Errno)
primitive mmap  : Size -> Prot -> Flags -> IO (Ptr + Errno)
```

### Browser (WASM)

```
primitive fetch : Request -> IO (Response + Error)
primitive setTimeout : Int -> (Unit -> IO Unit) -> IO TimerId
```

### Bare Metal

```
primitive gpioWrite : Pin -> Level -> IO Unit
primitive gpioRead  : Pin -> IO Level
primitive delayMicros : Int -> IO Unit
```

## Callbacks

Once can provide callbacks to foreign code:

```
type EventHandler = Event -> IO Unit

export registerHandler : EventHandler -> IO HandlerId
```

The callback is compiled to a C function pointer that foreign code can invoke.

## Summary

| Direction | Keyword | Purpose |
|-----------|---------|---------|
| Import | `primitive` | Call external functions |
| Export | `export` | Expose Once functions |
| Hide internals | `opaque` | Foreign types |

Once's FFI enables seamless integration with the C ecosystem while maintaining type safety within Once code. The lack of runtime overhead makes Once suitable as a library for performance-critical components.
