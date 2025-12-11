# Once and Unikernels

## Why Once Fits Unikernels

Unikernels are single-purpose, minimal OS images that include only what an application needs. Once's design aligns naturally with this philosophy:

| Unikernel Principle | Once Property |
|---------------------|---------------|
| Include only what you need | IO in types makes dependencies explicit |
| Single address space | No runtime isolation overhead |
| Minimal attack surface | Type-safe, no hidden behavior |
| Fast boot | No runtime initialization |
| No OS abstraction layers | Compiles to direct calls |

## Effects Declare Dependencies

In Once, the type signature declares exactly what external capabilities a function needs:

```
-- This function needs file system access
readConfig : Path -> IO (Config + Error)

-- This function needs network access
fetchData : Url -> IO (Response + Error)

-- This function is pure - needs nothing
parseJson : String -> Json + Error
```

A unikernel compiler can analyze these types and link **only** the required components:

```
-- Type analysis reveals:
-- - Needs filesystem primitives
-- - Needs network stack
-- - Does NOT need: graphics, audio, USB, etc.

main : IO Unit
main = bind (readConfig "app.conf") (\cfg ->
         bind (fetchData cfg.endpoint) (\data ->
           putLine (process data)
         )
       )
```

## The Three Strata and Unikernels

Once's three strata map cleanly to unikernel architecture:

```
┌─────────────────────────────────────────────────────┐
│  Interpretations (Unikernel primitives)             │
│  - Minimal OS services needed by this app           │
├─────────────────────────────────────────────────────┤
│  Derived (Application logic)                        │
│  - Pure computation, no OS dependencies             │
├─────────────────────────────────────────────────────┤
│  Generators (Categorical core)                      │
│  - The 12 primitives                                │
└─────────────────────────────────────────────────────┘
```

The Derived stratum (where most code lives) has **zero OS dependencies**. Only Interpretations touches the unikernel's OS layer.

## Building a Unikernel

### Step 1: Write Pure Application Logic

```
-- All in Derived stratum - pure, portable
type Request = { path : String, method : Method }
type Response = { status : Int, body : String }

router : Request -> Handler
router req = case req.method of
  GET  -> handleGet req.path
  POST -> handlePost req.path

handleGet : String -> Response
handleGet path = ...

handlePost : String -> Response
handlePost path = ...
```

### Step 2: Add IO at Boundaries

```
-- Thin IO wrapper in Interpretations
server : Int -> IO Unit
server port = bind (listen port) (\socket ->
  eventLoop (accept socket) handleRequest
)

handleRequest : Socket -> IO Unit
handleRequest sock =
  bind (readRequest sock) (\req ->
    let response = router req in
    writeResponse sock response
  )
```

### Step 3: Compile to Unikernel

```bash
# Compile with unikernel target
once build server.once --target=unikernel --os=solo5

# Output: server.bin (bootable image, ~2MB)
```

## Minimal Interpretation Layers

Different unikernel platforms need different interpretations:

### Solo5 (Minimal hypervisor interface)

```
-- Solo5 primitives
primitive solo5_net_read  : NetHandle -> IO (Bytes + Error)
primitive solo5_net_write : NetHandle * Bytes -> IO (Unit + Error)
primitive solo5_block_read  : BlockHandle * Offset -> IO (Bytes + Error)
primitive solo5_block_write : BlockHandle * Offset * Bytes -> IO (Unit + Error)
```

### MirageOS (OCaml-based)

```
-- Mirage primitives
primitive mirage_tcp_connect : Ip * Port -> IO (Flow + Error)
primitive mirage_tcp_read : Flow -> IO (Bytes + Error)
primitive mirage_tcp_write : Flow * Bytes -> IO (Unit + Error)
```

### OSv (Full POSIX compatibility)

```
-- Can use standard POSIX primitives
primitive read  : Fd * Size -> IO (Bytes + Errno)
primitive write : Fd * Bytes -> IO (Size + Errno)
```

## Size Comparison

| Component | Traditional OS | Once Unikernel |
|-----------|----------------|----------------|
| Kernel | ~100MB | ~1MB (Solo5) |
| Userspace | ~500MB+ | 0 (no separation) |
| Application | ~10MB | ~1MB |
| **Total** | ~600MB+ | **~2MB** |

The reduction comes from:
- No unused OS features
- No process isolation overhead
- Direct compilation to hardware interface
- Pure code needs no runtime support

## Security Benefits

Once's type system provides security guarantees that complement unikernel isolation:

### Capability-Based Security

```
-- The type declares required capabilities
type Capability = Network + Filesystem + None

-- Function can only use capabilities in its type
restrictedServer : Network -> IO Unit

-- Cannot access filesystem - not in the type!
```

### No Hidden State

```
-- IO is explicit - no hidden mutable state
-- Result type forces error handling - no uncaught exceptions
-- Linear types prevent resource leaks

safeHandler : Request^1 -> IO Response
```

### Minimal TCB

| Traditional Stack | Unikernel + Once |
|-------------------|------------------|
| OS kernel | Hypervisor |
| System libraries | Solo5/Mirage libs |
| Language runtime | None (compiled) |
| GC | None (linear types) |
| Application | Once application |

## QTT and Resource Management

Once's quantitative types are particularly valuable in unikernels:

```
-- Linear handle: must be closed exactly once
openFile : Path -> IO (Handle^1 + Error)
closeFile : Handle^1 -> IO Unit

-- Compiler ensures no handle leaks
-- No GC needed - ownership is tracked
```

This eliminates entire classes of resource bugs without runtime overhead.

## Example: Minimal HTTP Server

```
-- Pure request handling
handleHttp : HttpRequest -> HttpResponse
handleHttp req = case req.path of
  "/" -> ok "Hello from Once unikernel"
  "/health" -> ok "OK"
  _ -> notFound

-- IO wrapper
main : IO Unit
main =
  bind (tcpListen 8080) (\server ->
    forever (
      bind (tcpAccept server) (\conn ->
        bind (httpRead conn) (\req ->
          httpWrite conn (handleHttp req)
        )
      )
    )
  )
```

Compiles to a ~2MB bootable image that:
- Boots in milliseconds
- Uses ~16MB RAM
- Has minimal attack surface
- Can run on bare hypervisor

## Summary

| Aspect | Once Advantage |
|--------|----------------|
| Dependency analysis | IO types declare what's needed |
| Code size | Pure code has no OS dependencies |
| Security | Type system enforces capabilities |
| Resources | QTT eliminates GC and leaks |
| Boot time | No runtime initialization |
| Attack surface | Only included primitives are callable |

Once and unikernels are a natural fit. The language's explicit effect tracking, pure core, and quantitative types align perfectly with unikernel goals of minimalism, security, and performance.
