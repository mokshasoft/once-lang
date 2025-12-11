# Time in Once

## Coalgebraic Time

Once models time using **coalgebras** - the categorical dual of algebras. While algebras describe how to *construct* finite data (like lists), coalgebras describe how to *observe* potentially infinite behavior (like streams of events over time).

| Structure | Algebra (finite) | Coalgebra (infinite) |
|-----------|------------------|---------------------|
| Definition | `F A -> A` | `A -> F A` |
| Example | `List A = 1 + A * List A` | `Stream A = A * Stream A` |
| Operation | Fold (catamorphism) | Unfold (anamorphism) |
| Time model | Discrete history | Ongoing process |

## Streams

The primary time abstraction in Once is the **Stream**:

```
Stream A = A * Stream A
```

This is the **final coalgebra** of the functor `F X = A * X`. A stream is:
- A current value of type `A`
- Followed by the rest of the stream

Streams are infinite by construction - they always have a next element.

### Stream Operations

```
-- Observe the current value
head : Stream A -> A
head = fst

-- Advance to the rest
tail : Stream A -> Stream A
tail = snd

-- Create a stream from a generator
unfold : (S -> A * S) -> S -> Stream A

-- Map over all elements
mapStream : (A -> B) -> Stream A -> Stream B

-- Zip two streams
zipWith : (A -> B -> C) -> Stream A -> Stream B -> Stream C
```

### Example: Counter Stream

```
-- Generate natural numbers: 0, 1, 2, 3, ...
nats : Stream Int
nats = unfold (\n -> (n, n + 1)) 0

-- Take finite prefix
take : Int -> Stream A -> List A
take 0 _ = []
take n s = head s :: take (n - 1) (tail s)
```

## Event Streams and IO

Streams integrate with Once's IO monad for reactive programming:

```
-- A stream of events from the outside world
EventStream A = IO (Stream A)

-- Keyboard events
keyEvents : IO (Stream KeyEvent)

-- Mouse events
mouseEvents : IO (Stream MouseEvent)

-- Timer ticks
every : Duration -> IO (Stream Unit)
```

### Example: Event Loop

```
-- Main event loop pattern
eventLoop : IO (Stream Event) -> (State -> Event -> State) -> State -> IO Unit
eventLoop events step initial =
  bind events (\stream ->
    runStream stream initial step
  )

-- Process events until termination
runStream : Stream Event -> State -> (State -> Event -> State) -> IO Unit
```

## State Machines

State machines are coalgebras of the form `S -> A * S`:

```
-- A state machine: given state, produce output and next state
Machine S A = S -> A * S

-- Run a machine to produce a stream
runMachine : Machine S A -> S -> Stream A
runMachine machine = unfold machine

-- Compose machines
composeMachine : Machine S A -> Machine T B -> Machine (S * T) (A * B)
```

### Example: Toggle Switch

```
-- Toggle between on/off states
toggle : Machine Bool Bool
toggle state = (state, not state)

-- Produces: True, False, True, False, ...
toggleStream : Stream Bool
toggleStream = runMachine toggle True
```

## Discrete Time Steps

For discrete time simulation, Once uses indexed streams:

```
-- Value at each time step
type TimeSeries A = Stream A

-- Delay by one step (requires initial value)
delay : A -> Stream A -> Stream A
delay initial stream = unfold step (initial, stream)
  where step (prev, s) = (prev, (head s, tail s))

-- Feedback loop (for recursive definitions)
feedback : A -> (Stream A -> Stream A) -> Stream A
```

### Example: Fibonacci

```
-- Fibonacci sequence as a stream
fibs : Stream Int
fibs = unfold step (0, 1)
  where step (a, b) = (a, (b, a + b))

-- 0, 1, 1, 2, 3, 5, 8, 13, ...
```

## Temporal Operators

Common temporal operators from reactive programming:

```
-- Sample stream at events
sample : Stream A -> Stream Unit -> Stream A

-- Hold last value until next event
hold : A -> Stream (Maybe A) -> Stream A

-- Accumulate over time
scan : (B -> A -> B) -> B -> Stream A -> Stream B

-- Filter events
filter : (A -> Bool) -> Stream A -> Stream (Maybe A)

-- Merge two event streams
merge : Stream (Maybe A) -> Stream (Maybe A) -> Stream (Maybe A)
```

## Time and Linearity

Once's QTT interacts with temporal structures:

```
-- Linear stream: each element used exactly once
LinearStream A = Stream (A^1)

-- Affine stream: elements may be dropped
AffineStream A = Stream (Maybe A^1)
```

Linear streams guarantee that every event is processed exactly once - useful for resource management over time.

## Comparison with Other Approaches

| Approach | Model | Once Equivalent |
|----------|-------|-----------------|
| FRP (Elm, Reflex) | Signals + Events | Streams + IO |
| Rx (RxJS, RxJava) | Observables | `IO (Stream A)` |
| Async/await | Promises | `IO A` (single value) |
| CSP (Go channels) | Channels | `Stream A` with effects |

## Categorical Perspective

Streams arise from the **final coalgebra** construction:

```
-- The functor
F : Type -> Type
F X = A * X

-- Stream is the final coalgebra
Stream A = νX. A * X

-- Universal property: any coalgebra factors through Stream
unfold : (S -> A * S) -> S -> Stream A
```

This means `Stream A` is the "largest" type satisfying the stream equation - it contains all possible infinite sequences.

## Anamorphisms

The dual of catamorphism (fold) is **anamorphism** (unfold):

```
-- Catamorphism: consume finite data
cata : (F A -> A) -> Fix F -> A

-- Anamorphism: produce infinite data
ana : (A -> F A) -> A -> Cofix F
```

For streams:
```
-- Unfold is the anamorphism for streams
unfold : (S -> A * S) -> S -> Stream A
ana = unfold
```

## Summary

| Concept | Once Approach |
|---------|---------------|
| Infinite sequences | `Stream A = A * Stream A` |
| Generation | `unfold : (S -> A * S) -> S -> Stream A` |
| Observation | `head`, `tail` |
| IO integration | `IO (Stream Event)` for event sources |
| State machines | `S -> A * S` coalgebras |
| Temporal operators | `scan`, `sample`, `hold`, `merge` |
| Linearity | `Stream (A^1)` for resource safety |

Time in Once is modeled coalgebraically. Streams represent ongoing processes, state machines capture stateful behavior, and the IO monad connects pure temporal abstractions to real-world event sources.
