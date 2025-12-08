# Once and Unikernels

## The Perfect Match

Unikernels are single-purpose, library OS images that include only what an application needs. Once's design philosophy aligns perfectly with this:

| Unikernel Principle | Once Property |
|---------------------|---------------|
| Include only what you need | Effects explicit in types |
| Single address space | No runtime isolation needed |
| No OS abstraction overhead | Compiles to direct calls |
| Minimal attack surface | Type-safe, no hidden behavior |
| Boot in milliseconds | No runtime initialization |

## Why Natural Transformations Enable This

### 1. Effects as Capabilities

```
type WebServer = Network * State * Halts

-- The TYPE tells you exactly what OS services are needed:
-- - Network: TCP/IP stack
-- - State: memory for connections
-- - Halts: graceful shutdown
```

A unikernel compiler can look at the effect types and link **only** the required OS components:

```
Effect          → Linked Component
────────────────────────────────────
Network         → minimal TCP/IP stack
State           → memory allocator
Halts           → shutdown handler
FileSystem      → (not present, not linked)
Threads         → (not present, not linked)
```

### 2. No Hidden Dependencies

Traditional approach:
```c
#include <stdlib.h>  // pulls in malloc, free, atexit, ...
#include <stdio.h>   // pulls in FILE, buffering, locale, ...
// You get megabytes of code you don't use
```

Once approach:
```
myServer : Network * State -> Response
-- Type signature IS the dependency manifest
-- Nothing hidden, nothing extra
```

### 3. Composition Without Overhead

Natural transformations compose at compile time:

```
handleRequest : Request -> Network (Response)
parseBody     : Body -> State (Parsed)
validate      : Parsed -> Halts + Valid

-- Composed:
pipeline : Request -> Network * State * Halts (Valid)
pipeline = compose validate (compose parseBody handleRequest)

-- Compiles to direct function calls, no indirection
```

## Unikernel Architecture with Once

```
┌─────────────────────────────────────────┐
│           Once Application              │
│  ┌─────────────────────────────────┐   │
│  │  Business Logic (Derived)       │   │
│  │  - Natural transformations      │   │
│  │  - Categorical composition      │   │
│  └─────────────────────────────────┘   │
│                  │                      │
│                  ▼                      │
│  ┌─────────────────────────────────┐   │
│  │  Effect Handlers (Interpretations)│  │
│  │  - Network → driver calls       │   │
│  │  - State → memory ops           │   │
│  │  - Console → UART/VGA           │   │
│  └─────────────────────────────────┘   │
│                  │                      │
├──────────────────┼──────────────────────┤
│                  ▼                      │
│  ┌─────────────────────────────────┐   │
│  │  Minimal OS Layer               │   │
│  │  - Boot code                    │   │
│  │  - Interrupt handlers           │   │
│  │  - Driver stubs                 │   │
│  └─────────────────────────────────┘   │
│                  │                      │
└──────────────────┼──────────────────────┘
                   ▼
            ┌──────────┐
            │ Hardware │
            └──────────┘
```

## Effect-Driven Linking

### The Compiler Workflow

```
1. Parse Once program
2. Type check (extract effect signature)
3. Analyze: which effects are used?
4. Link: include only those OS components
5. Generate: single bootable image
```

### Example

```
-- Source
main : Console * Halts -> Unit
main = compose output (constant "Hello, Unikernel!")
```

```
Effects detected: Console, Halts

Linking:
  ✓ boot.o          (always needed)
  ✓ console.o       (Console effect)
  ✓ halt.o          (Halts effect)
  ✗ network.o       (not used)
  ✗ filesystem.o    (not used)
  ✗ memory.o        (no State effect)

Final image: 12 KB
```

## Comparison with Existing Unikernel Approaches

| System | Language | Effect Tracking | Image Size |
|--------|----------|-----------------|------------|
| **MirageOS** | OCaml | Module functors | Small |
| **HaLVM** | Haskell | Manual | Medium (GHC RTS) |
| **IncludeOS** | C++ | Manual | Small |
| **Unikraft** | C | Manual/Kconfig | Very small |
| **Once** | Once | Automatic (types) | Minimal |

The advantage: **types tell you dependencies automatically**.

## Security Benefits

### 1. Minimal Attack Surface

```
webApp : Network * State -> Response
-- No filesystem effect = no filesystem vulnerabilities
-- No exec effect = no shell injection possible
-- No dynamic loading = no library injection
```

### 2. Type-Enforced Isolation

Natural transformations are **pure** by default. Side effects are:
- Explicit in the type
- Limited to declared capabilities
- Auditable at compile time

### 3. No Runtime Exploits

| Attack Vector | Once Status |
|--------------|-------------|
| Buffer overflow | Types prevent (sized arrays) |
| Use-after-free | Linear analysis catches |
| ROP/JOP | Minimal code surface |
| Heap spray | No dynamic heap (optional) |

## Example: Minimal Web Server

```
-- Effect signature declares ALL capabilities
type WebApp = Network * State * Halts

server : Port -> WebApp -> Unit
server port =
  compose respond
    (compose handleRequest
      (compose accept
        (listen port)))

-- This compiles to a ~50KB unikernel:
-- - TCP/IP stack (no UDP, no ICMP)
-- - Static routes only (from State)
-- - No TLS (not in effects)
-- - No logging (no Console effect)
```

## The Vision

```
┌──────────────────────────────────────────────────────┐
│                                                      │
│   Write pure business logic in Derived layer.       │
│   Effects visible in types.                         │
│                                                      │
│                      ▼                               │
│                                                      │
│   Compiler extracts effect requirements             │
│   automatically from types.                          │
│                                                      │
│                      ▼                               │
│                                                      │
│   Linker includes only needed OS components.        │
│   Dead code elimination on OS itself.               │
│                                                      │
│                      ▼                               │
│                                                      │
│   Output: minimal, secure, bootable image.          │
│   Millisecond boot. Kilobyte size.                  │
│                                                      │
└──────────────────────────────────────────────────────┘
```

## Conclusion

Natural transformations + unikernels =

1. **Type-driven minimal images** - Effects declare dependencies
2. **Zero-overhead composition** - Compile-time fusion
3. **Security by construction** - No capabilities = no vulnerabilities
4. **Instant boot** - No runtime to initialize
5. **Auditable** - Read the types, know the attack surface

Once's categorical foundation isn't just mathematically elegant - it's **operationally optimal** for building minimal, secure, single-purpose systems.
