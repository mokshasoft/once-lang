# Input/Output in Once

## IO is a Monad

Once is honest: `IO` is a monad. This gives us three levels of composition, each more powerful than the last.

```
Functor ⊂ Applicative ⊂ Monad
```

If you know what a monad is, you know how Once's IO works. If you don't, this document explains the three levels of composition.

## The Three Levels

### Level 1: Functor

Transform the result of an IO operation without changing the effect:

```
fmap : (A -> B) -> IO A -> IO B
```

Example:
```
-- readFile returns IO String
-- We want IO Int (the length)
fileLength : Path -> IO Int
fileLength path = fmap length (readFile path)
```

`fmap` lets you work with the value "inside" the IO without extracting it. The IO effect is preserved.

### Level 2: Applicative

Combine independent IO operations:

```
pure : A -> IO A
both : IO A -> IO B -> IO (A * B)
```

Example:
```
-- Read two files independently
readBoth : Path -> Path -> IO (String * String)
readBoth p1 p2 = both (readFile p1) (readFile p2)
```

`both` runs two IO operations and pairs their results. The operations are independent - neither depends on the other's result. This means they could potentially run in parallel.

`pure` lifts a pure value into IO (an IO operation that does nothing and returns the value).

### Level 3: Monad

Sequence dependent IO operations - where the second depends on the first's result:

```
bind : IO A -> (A -> IO B) -> IO B
```

Example:
```
-- Read a config file, then read the file it points to
readIndirect : Path -> IO String
readIndirect configPath = bind (readFile configPath) (\config ->
  readFile (parsePath config)
)
```

`bind` is the most powerful - the second operation can depend on the result of the first. This is sequential by nature.

## When to Use Each Level

| Level | Use When | Example |
|-------|----------|---------|
| Functor | Transforming a result | `fmap toUpper readLine` |
| Applicative | Combining independent effects | `both (readFile a) (readFile b)` |
| Monad | Second depends on first | `bind getConfig (\c -> loadFile c)` |

**Prefer the weakest level that works:**
- Functor when you're just transforming
- Applicative when operations are independent
- Monad only when there's true dependency

This isn't just style - applicative operations can parallelize, monadic ones cannot.

## IO Unit

`IO Unit` means "an IO operation that performs an effect but returns no meaningful value":

```
putLine : String -> IO Unit      -- prints, returns nothing
writeFile : Path * String -> IO Unit  -- writes, returns nothing
```

Compare to operations that return useful values:
```
readFile : Path -> IO String     -- returns file contents
getLine : Unit -> IO String      -- returns user input
```

`Unit` is the terminal object (the type with exactly one value). `IO Unit` means "run this for its effect, not its result."

## The Monad Laws

`IO` satisfies the monad laws:

```
-- Left identity
bind (pure a) f  ≡  f a

-- Right identity
bind m pure  ≡  m

-- Associativity
bind (bind m f) g  ≡  bind m (\x -> bind (f x) g)
```

These laws ensure composition behaves predictably.

## Categorical Perspective

A monad is a monoid in the category of endofunctors:

```
IO : Type -> Type              -- endofunctor
pure : A -> IO A               -- unit (η)
join : IO (IO A) -> IO A       -- multiplication (μ)
```

`bind` is derived from `fmap` and `join`:
```
bind m f = join (fmap f m)
```

The monad laws are the monoid laws (identity and associativity) lifted to endofunctors.

## Primitives

IO operations come from **primitives** in the Interpretations layer:

```
-- File operations
primitive readFile  : Path -> IO (String + Error)
primitive writeFile : Path * String -> IO (Unit + Error)

-- Console
primitive getLine : Unit -> IO String
primitive putLine : String -> IO Unit

-- Network
primitive httpGet : Url -> IO (Response + Error)
```

Primitives are opaque - they have no implementation in Once, only a type signature. The interpretation (POSIX, bare metal, WASM) provides the implementation.

## Composition Example

A complete example using all three levels:

```
-- Configuration type
type Config = { dataPath : Path, outputPath : Path }

-- Parse config from string (pure)
parseConfig : String -> Result Config ParseError

-- Process data (pure)
processData : String -> String

-- The full pipeline
pipeline : Path -> IO (Result Unit Error)
pipeline configPath =
  bind (readFile configPath) (\configResult ->
    case configResult of
      err e -> pure (err e)
      ok configStr ->
        case parseConfig configStr of
          err e -> pure (err e)
          ok config ->
            bind (readFile config.dataPath) (\dataResult ->
              case dataResult of
                err e -> pure (err e)
                ok data ->
                  let result = processData data in
                  writeFile (config.outputPath, result)
            )
  )
```

Notice:
- `parseConfig` and `processData` are pure - no IO
- `readFile` and `writeFile` are IO primitives
- `bind` sequences the dependent operations
- Error handling uses `Result` (sum types, see D025)

## IO and Purity

The type tells you everything:

```
-- Pure: no IO in the type
process : String -> String

-- Effectful: IO in the type
load : Path -> IO String
```

You cannot accidentally do IO. If a function doesn't have `IO` in its type, it cannot perform IO. This is enforced by the type system.

## Comparison with Other Approaches

| Language | IO Approach | Once Equivalent |
|----------|-------------|-----------------|
| Haskell | IO monad | Same - IO is a monad |
| Rust | No pure/impure distinction | Primitives only in Interpretations |
| OCaml | Impure by default | N/A (Once tracks effects in types) |
| Scala | IO monad (cats-effect, ZIO) | Same concept |

## Summary

| Concept | Once Approach |
|---------|---------------|
| IO type | `IO A` - a monad |
| Transform results | `fmap : (A -> B) -> IO A -> IO B` |
| Combine independent | `both : IO A -> IO B -> IO (A * B)` |
| Sequence dependent | `bind : IO A -> (A -> IO B) -> IO B` |
| Lift pure value | `pure : A -> IO A` |
| Effect only | `IO Unit` - run for effect, not result |
| IO operations | Primitives in Interpretations layer |
| Purity tracking | IO in type = effectful, no IO = pure |

Once is honest about IO being a monad. Use the weakest level of composition that works: functor for transforms, applicative for independent operations, monad for true dependencies.
