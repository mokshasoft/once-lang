# Input/Output in Once

## The Principle

Once has no special IO construct. There is no IO monad, no effect system syntax, no special keywords. IO is handled through:

1. **Opaque primitives** - Morphisms declared at the boundary with the external world
2. **Functor choice** - Which functors you transform between determines effects
3. **Composition** - Everything else is just natural transformation composition

## Opaque Primitives

At the boundary between Once and the external world, certain morphisms are declared as **primitives**:

```
-- These are provided by the Interpretation layer
-- They have no internal structure in Once

primitive read_byte  : FileHandle -> Byte
primitive write_byte : FileHandle * Byte -> Unit
primitive open_file  : Path -> FileHandle + Error
primitive close_file : FileHandle -> Unit
```

These primitives are:
- **Opaque** - No implementation in Once, provided by the environment
- **Declared at boundaries** - Not scattered through the code
- **Composable** - They're morphisms like any other

Everything else is pure composition of natural transformations.

## Effects as Functor Choice

Effects aren't a language feature - they emerge from which functors appear in your types:

| Transformation Type | Effect |
|---------------------|--------|
| `A -> A` | Pure (endomorphism) |
| `A -> Maybe B` | Partiality (might fail) |
| `A -> List B` | Nondeterminism (multiple results) |
| `A -> (S -> S * B)` | State (reads/writes state S) |
| `A -> E + B` | Errors (might produce E) |
| `A -> External B` | IO (requires external primitive) |

The type tells you everything. The compiler infers quantities and can report effects:

```
> once analyze myFunction

myFunction : String^ω -> Maybe (List Result)
  Uses: Partiality, Nondeterminism
  Does not use: State, IO
  Quantity: ω (unrestricted, uses diagonal)
```

Quantities are enforced by the type system via QTT. See [Memory](memory.md) for details.

## Referential Transparency

In Once, referential transparency is about **which equations hold**.

A pure morphism `f : A -> B` satisfies:
- `f = f` (trivially)
- Can be substituted anywhere
- Order of evaluation doesn't matter

An effectful morphism like `read_byte : FileHandle -> Byte`:
- Still composes correctly
- But the **interpretation** involves the external world
- The categorical laws still hold - just in a different category

The insight: pure and effectful code live in **different categories**. Within each, the equations hold. The boundary (primitives) is where categories meet.

## No Hidden Effects

In Once, you cannot accidentally do IO:

```
-- This type signature tells you everything
processData : String -> Result

-- This CANNOT do IO - no External functor in the type
-- This CANNOT mutate state - no State functor
-- This CANNOT fail - no Maybe/Either
```

If a function needs IO, it must say so:

```
-- The External functor appears in the type
loadConfig : Path -> External (Config + Error)
```

## Composition of Effectful Code

Effectful code composes like any other natural transformation:

```
-- Pure
parse : String -> AST + Error
validate : AST -> AST + Error
transform : AST -> AST

-- Compose (all pure, error-tracking)
pipeline : String -> AST + Error
pipeline = compose transform (compose validate parse)

-- With IO
readFile : Path -> External (String + Error)
writeFile : Path * String -> External (Unit + Error)

-- Compose pure with effectful at boundaries
processFile : Path -> External (Unit + Error)
processFile = compose
  (compose writeOutput pipeline)
  readFile
```

## The External Functor

`External` is Once's way of marking "this requires the outside world":

```
-- External is a functor
fmap : (A -> B) -> (External A -> External B)

-- Primitives produce External values
read_byte : FileHandle -> External Byte

-- You can map pure functions over External
processInput : External String -> External Result
processInput = fmap parse
```

`External` is **not magic** - it's just a functor. The magic is in the primitives that produce `External` values, which are provided by the Interpretation layer.

## Streaming IO

For ongoing IO (like event loops), Once uses coalgebraic streams:

```
-- A stream of values over time
Stream : Type -> Type
Stream A = A * Stream A   -- head and tail (coinductive)

-- Unfold a stream from a seed
unfold : (S -> A * S) -> S -> Stream A

-- An event loop
type EventLoop = External (Stream Event)

-- Main program that handles events
main : EventLoop -> Stream Response
main = fmap (map handleEvent)
```

Streams are infinite structures unfolded via anamorphism. Time is modeled coalgebraically.

## Console Example

A simple console program:

```
-- Primitives (from Interpretation layer)
primitive getChar : Unit -> External Char
primitive putChar : Char -> External Unit

-- Derived
putString : String -> External Unit
putString = foldl (compose putChar) (terminal Unit)

getLine : Unit -> External String
getLine = unfold step ""
  where step acc = case getChar () of
    '\n' -> (acc, Nothing)
    c    -> (acc, Just (acc ++ [c]))

-- Main program
main : Unit -> External Unit
main = compose putString (pair (constant "Hello, ") getLine)
```

## Comparison with Other Approaches

| Approach | How IO is Marked | Once Equivalent |
|----------|------------------|-----------------|
| Haskell IO Monad | `IO a` type | `External a` functor |
| Effect systems | Effect list in type | Functor composition in type |
| Rust | No pure/impure distinction | Primitives only in Interpretations |
| C | No marking at all | N/A (Once always marks) |

## Summary

| Concept | Once Approach |
|---------|---------------|
| IO operations | Opaque primitives in Interpretation layer |
| Effect tracking | Functors in the type signature |
| Purity | Absence of External/State/etc functors |
| Composition | Same as pure code - natural transformations |
| Streaming | Coalgebraic streams via unfold |
| Analysis | Tools report which effects are used |

In Once, IO is not special. It's morphisms that happen to be primitives, composed with natural transformations like everything else. The type tells you what effects are involved.
