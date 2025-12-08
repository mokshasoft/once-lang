# Time in Once

## Categorical Models of Time

Time can be modeled categorically in several ways:

| Model | Categorical Structure | Once Type |
|-------|----------------------|-----------|
| **Streams** | Final coalgebra of `A * (-)` | `Stream` |
| **State machines** | Coalgebras `S -> A * S` | `Transition` |
| **Events** | State with output | `Event` |
| **Discrete steps** | Endofunctor iteration | via `Fix` |
| **Causality** | Arrow with delay | (can be added) |

## Once's Time Types

### Stream: Infinite Time

```
Stream A = Fix (Along A)
-- Expands to: Fix (λX. A * X)
-- An infinite sequence: a₀, a₁, a₂, a₃, ...
```

This is the **final coalgebra** of the functor `A * (-)`. It represents:
- Infinite discrete time
- A value at every time step
- No beginning, no end

```
Stream A = (A, Stream A)
         = (a₀, (a₁, (a₂, (a₃, ...))))

Time:      t=0  t=1  t=2  t=3  ...
```

### Transition: State Over Time

```
Transition S A = S -> A * S
-- "Given current state, produce output and next state"
```

This is a **Mealy machine** - the fundamental model of stateful computation over time:

```
         ┌─────────┐
input →  │ current │ → output
         │  state  │
         └────┬────┘
              │
              ▼
         next state
```

### Event: Discrete Happenings

```
Event S A = S -> A * S
-- Same structure as Transition
-- Semantically: something that happens and changes state
```

## The Coalgebraic View

Time is naturally **coalgebraic**. Where algebras fold up (catamorphism), coalgebras unfold (anamorphism):

```
-- Algebra (fold): consuming time
cata : (F A -> A) -> Fix F -> A

-- Coalgebra (unfold): producing time
ana : (A -> F A) -> A -> Fix F
```

### Stream as Coalgebra

```
-- The coalgebra for streams
unfold : (S -> A * S) -> S -> Stream A
unfold step seed =
  let (value, next) = step seed
  in value :< unfold step next

-- In Once:
ana : (S -> A * S) -> S -> Stream A
```

## Time Operators

| Concept | Categorical | Once |
|---------|-------------|------|
| Current value | `head : Stream A -> A` | `head` |
| Advance time | `tail : Stream A -> Stream A` | `tail` |
| Unfold | `ana : (S -> F S) -> S -> Fix F` | `ana` |
| Fold | `cata : (F A -> A) -> Fix F -> A` | `cata` |

## Discrete vs Continuous Time

### Discrete Time (Once has this)

```
Stream A = A * Stream A
-- Time steps: 0, 1, 2, 3, ...
-- Each step produces one value
```

### Continuous Time (could be added)

For continuous time, you'd model time as a parameter:

```
Continuous A = Time -> A
-- where Time = ℝ or a dense order

-- Or as a limit of discrete samples
Signal A = Stream (Time * A)
```

## Causality

A **causal** function is one where output at time `t` depends only on inputs at times `≤ t`:

```
-- Causal arrow (conceptual)
Causal A B = Stream A -> Stream B
-- with constraint: (output !! n) depends only on (take (n+1) input)
```

In categorical terms, causal functions are **natural transformations** between stream functors that respect the coalgebra structure.

### The Delay Operator

The key primitive for causal systems:

```
delay : A -> Stream A -> Stream A
delay initial stream = initial :< stream

-- Categorically: the "later" modality ▷
-- ▷A means "A at the next time step"
```

## Temporal Types (Extension)

Once could be extended with explicit temporal modalities:

```
-- "Later" modality
Later A = Stream A  -- first element is "now", rest is "later"

-- "Always" (□)
Always A = Stream A  -- A at all future times

-- "Eventually" (◇)
Eventually A = Fix (Maybe * (-))  -- A at some future time
```

## State Machines Over Time

The `Transition` type is a Moore/Mealy machine:

```
Transition S A = S -> A * S

-- Run for n steps
run : Transition S A -> S -> Stream A
run trans initial = ana trans initial
```

### Example: Counter

```
counter : Transition Int Int
counter = \n -> (n, n + 1)

-- run counter 0 = [0, 1, 2, 3, 4, ...]
```

## FRP (Functional Reactive Programming)

Once's primitives can encode FRP:

```
-- Behavior: value over time
Behavior A = Stream A

-- Event: occasional occurrences
EventStream A = Stream (Maybe A)

-- Signal function: transforms time-varying values
SF A B = Behavior A -> Behavior B
-- This is just a causal stream transformer
```

### FRP Combinators

```
-- Sample behavior at events
sample : Behavior A -> EventStream B -> EventStream A

-- Integrate over time (for continuous)
integrate : Behavior Double -> Behavior Double

-- Switch behaviors
switch : Behavior A -> EventStream (Behavior A) -> Behavior A
```

## Time and Effects

Time interacts with effects via composition:

```
type TimeState A = State S (Stream A)
-- Stateful computation that also produces a stream of values

type EventLoop = Console * State * Halts -> Stream Event
-- An event loop: console I/O, state, can halt, produces events over time
```

## Compilation of Time

### Discrete Time → Event Loop

```
-- Source
main : Stream Action -> Stream Reaction
main = fmap respond

-- Compiled (event loop)
while (true) {
    Action a = read_input();
    Reaction r = respond(a);
    write_output(r);
}
```

### State Machine → State Variable

```
-- Source
machine : Transition Int Int
machine = \s -> (s * 2, s + 1)

-- Compiled
int state = 0;
while (true) {
    int output = state * 2;
    emit(output);
    state = state + 1;
}
```

## Summary

| Time Concept | Once Encoding |
|--------------|---------------|
| Infinite sequence | `Stream = Fix (Along A)` |
| State evolution | `Transition = S -> A * S` |
| Discrete event | `Event` |
| Step forward | `ana` (anamorphism) |
| Collapse time | `cata` (catamorphism) |
| Causality | Natural transformations on Stream |

Time in Once is **coalgebraic** - it's about unfolding structure rather than folding it up. This matches intuition: time flows forward, producing new states and values as it goes.
