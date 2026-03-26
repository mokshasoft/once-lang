# Once Best Practices

*Real-world patterns for a total, productive language*

---

## Part 1: Look What You Can Do

### 1. The Immortal Server

#### The Problem

Here's a simplified example of code that can go wrong:

```python
# Simplified example — real production code is more careful,
# but these patterns still appear in subtle forms
def handle_request(req):
    while not validate(req):      # What if validate() is buggy?
        req = try_fix(req)        # What if this loops forever?
    return process(req)           # Never reached

def run():
    while True:                   # "It runs forever" (hopefully)
        req = accept()
        resp = handle_request(req)  # Might hang here
        send(resp)
```

Real production code uses timeouts, watchdogs, health checks, and circuit breakers. These work, but they're runtime mitigations for problems that could be caught statically.

#### The Once Way

```once
-- A server is a transformation of streams
server : Stream Request → Stream Response
server = map handle

-- Each handler is total: it MUST return
handle : Request → Response
handle req = case validate req of
    Valid   → process req
    Invalid → errorResponse "bad request"

-- The "infinite loop" is just the infinite input stream
main : IO Unit
main = runServer server (listen 8080)
```

**What's different:**

1. **`handle` must return.** It's not a suggestion — if `handle` could loop forever, it wouldn't typecheck. The type `Request → Response` means "given a request, you WILL produce a response."

2. **No `while True`.** The server processes a `Stream Request`. The infinity comes from the input, not from a loop you wrote.

3. **Progress is guaranteed.** For every request that arrives, a response is produced. The type system enforces this.

4. **Graceful shutdown is free.** When the input stream ends (socket closed, shutdown signal), the output stream ends. No special handling needed.

#### "But What If I Need State?"

```once
-- Server with connection counting
serverWithState : Stream Request → Stream (Response, Stats)
serverWithState = statefulMap update initialStats
  where
    initialStats = { connections = 0, errors = 0 }

    update : Stats → Request → (Response, Stats)
    update stats req =
      let resp = handle req
          newStats = stats { connections = stats.connections + 1 }
      in (resp, newStats)
```

The state flows through the transformation. No mutable variables, no locks, no race conditions.

#### "But What About Effects?"

The pure version is a simplification. Real handlers do IO — database queries, external APIs, logging. Once separates these concerns:

```once
-- Pure transformation (the recursion structure):
server : Stream Request → Stream Response
server = map handle

-- But handle is pure! For real IO, we need Eff:
handleEff : Eff Request Response
handleEff = arr parseRequest
        >>> queryDatabase
        >>> arr formatResponse

-- Effectful server uses traverseEff:
serverEff : Eff (Stream Request) (Stream Response)
serverEff = traverseEff handleEff
```

**What's happening:**
- `Eff A B` is an effectful arrow (not a monad, an Arrow in the categorical sense)
- `arr : (A → B) → Eff A B` lifts pure functions into the effect context
- `>>> : Eff A B → Eff B C → Eff A C` composes effects sequentially

**The key insight:** Effects compose with recursion schemes through the carrier type:

```once
-- Pure fold (carrier = Int)
sum : List Int → Int
sum = Cata alg where alg Nil = 0; alg (Cons x r) = x + r

-- Effectful fold (carrier = Eff Unit Int)
sumWithIO : List Int → Eff Unit Int
sumWithIO = Cata alg where
    alg Nil = arr (const 0)
    alg (Cons x restEff) = logInt x >>> restEff >>> arr (+ x)
```

The recursion scheme (`Cata`) is the same. The algebra handles effects with `>>>`. No special "effectful Cata" needed.

**The separation:**
- **Recursion structure** (Cata, Ana, Hylo) — pure, total, structural
- **Leaf operations** (database query, API call) — effectful, sequenced with `>>>`

Totality applies to the recursion structure. Each algebra/coalgebra step completes (producing an `Eff` value), and those effects are sequenced.

**For complex patterns** (short-circuiting, parallelism), Once provides additional Arrow combinators:
- `first`/`second` — thread state alongside effects
- `(***)` — parallel effect composition
- `(|||)` — branch effects based on sum types (ArrowChoice)

See the [categorical deep dive](structured-recursion.md#arrow-infrastructure) for details.

#### "But What About Timeouts?"

```once
-- Bounded request handling
handleWithTimeout : Duration → Request → Eff Response
handleWithTimeout limit req =
    raceEff (processEff req) (timeoutEff limit)
```

The `raceEff` runs two effectful computations, returning whichever completes first. This is Arrow-based concurrency.

#### Why This Can't Go Wrong

In Once, you literally cannot write:

```once
-- TYPE ERROR: infinite recursion has no base case
brokenHandle : Request → Response
brokenHandle req = brokenHandle req  -- Rejected!
```

The recursion schemes require structural recursion. A function that calls itself without making progress toward a base case isn't expressible.

#### "But What About While Loops?"

You might think: "Sometimes I need `while (condition)` — that's not structural recursion!"

Let's examine what "while loops" actually are in practice:

| You write... | You actually mean... | Once equivalent |
|--------------|---------------------|-----------------|
| `while (running)` server loop | Process stream of requests | `map handle : Stream Req → Stream Resp` |
| `while (playing)` game loop | Transform input to frames | `ana step : State → Stream Frame` |
| `while (!converged)` Newton | Iterate until convergence | `obsWhile (not ∘ converged) iterations` |
| `while (tokens)` parsing | Consume token list | `Cata parseAlg tokens` |
| `while (lo < hi)` binary search | Search over bounded space | `Cata searchAlg searchSpace` |

**The pattern:** Every practical "while loop" either:
1. **Is structural** — iterating over a data structure → use `Cata`
2. **Should be bounded** — for safety → use `obs`, `obsWhile`
3. **Is a stream transformation** — infinite in, infinite out → use `Ana`, `map`

**What about truly unbounded loops?** Like the Collatz conjecture:
```python
while n != 1:
    n = n // 2 if n % 2 == 0 else 3 * n + 1
```

This is mathematically interesting but:
- It's an unsolved problem whether it terminates for all inputs
- No practical application needs this pattern
- If your code looks like this, you're missing a bound

**The uncomfortable truth:** If you think you need an unbounded numeric loop, you're probably:
1. **Missing the data structure** — there's a list, tree, or stream hiding in your problem
2. **Missing a bound** — for safety, you should limit iterations anyway
3. **Writing a mathematical curiosity** — not production code

**The deeper truth:** If an algorithm truly may never terminate, it's not a good algorithm — it's a bug or an unsolved problem.

Consider the "counterexamples" to structured recursion:

| "Needs unbounded loop" | Actually... |
|------------------------|-------------|
| Dataflow analysis | Lattice has finite height h → at most h×n iterations → bounded |
| Consensus (Paxos/Raft) | Terminates with bounds; without bounds, FLP impossibility applies |
| Garbage collection | Heap is finite → tracing is Cata over reachable objects |
| SAT solving | Search tree is finite → terminates (may be slow, but terminates) |
| Training "until convergence" | Either convergence is proven (structure exists) or bound by epochs |

Good algorithms either:
1. **Terminate by structure** — the data is finite (Cata)
2. **Terminate by proof** — math guarantees convergence (hidden structure)
3. **Are explicitly bounded** — timeout, max iterations (obs n, obsWhile)

An "algorithm" that genuinely might loop forever isn't an algorithm — it's a partial function with undefined behavior. That's not a feature to support; it's a bug to prevent.

Once doesn't restrict you from writing useful programs. It restricts you from writing programs that might not be programs at all.

**A challenge:** If you believe you have a legitimate algorithm that requires unbounded iteration and doesn't fit Cata/Ana/Hylo + observation, we'd like to hear about it. So far, every proposed counterexample has either had hidden structure (making it expressible) or lacked termination guarantees (making it a bug, not an algorithm).

---

### 2. The Fearless Parser

#### The Problem Everyone Has

```javascript
// Parser that haunts your dreams
function parse(input) {
    let pos = 0;
    while (pos < input.length) {
        // 47 different branches
        // Some increment pos, some don't
        // Some call parse() recursively
        // Good luck knowing if this terminates
    }
    return ast;
}
```

Parser bugs are legendary:
- Infinite loops on malformed input
- Stack overflows on deeply nested structures
- Memory exhaustion on large files
- "Works on my machine" with different inputs

#### The Once Way

```once
-- A parser consumes input and produces structure
-- The type TELLS you it's total
parseJson : List Char → Maybe Json

parseJson = Cata alg ∘ tokenize
  where
    alg : TokenF (Maybe Json) → Maybe Json
    alg EndOfInput = Nothing
    alg (ObjectStart fields) = Just (JsonObject fields)
    alg (ArrayStart items) = Just (JsonArray items)
    alg (StringToken s) = Just (JsonString s)
    alg (NumberToken n) = Just (JsonNumber n)
    alg (Invalid _) = Nothing  -- Malformed input → Nothing, not hang
```

**Why it can't hang:**

1. **`Cata` is structural recursion.** It consumes the token list one element at a time, always making progress toward the end.

2. **Every case is handled.** The `alg` function must handle every constructor of `TokenF`. No "oops, forgot that case."

3. **`Maybe` for failure.** Bad input returns `Nothing`, not an exception, not a hang.

#### Streaming Parser (Constant Memory)

```once
-- Parse a gigabyte file without loading it all
parseHugeFile : Stream Char → Stream Event

parseHugeFile = Ana coalg ∘ tokenizeStream
  where
    coalg : TokenStream → (Event, TokenStream)
    coalg tokens =
        let (event, rest) = parseNextEvent tokens
        in (event, rest)
```

The `Ana` produces output events one at a time as input arrives. Memory usage is bounded by the largest single event, not the file size.

#### "But What About Recursive Grammars?"

```once
-- JSON can nest arbitrarily deep
-- But the PARSE is still structural over the INPUT

parseValue : List Token → (Maybe Json, List Token)
parseValue tokens = case tokens of
    [] → (Nothing, [])
    (TokLBrace :: rest) → parseObject rest
    (TokLBracket :: rest) → parseArray rest
    (TokString s :: rest) → (Just (JsonString s), rest)
    (TokNumber n :: rest) → (Just (JsonNumber n), rest)
    _ → (Nothing, tokens)  -- Can't parse → fail cleanly
```

The recursion follows the *input structure*, not the *output structure*. Each recursive call consumes tokens, guaranteeing progress.

#### Why This Can't Go Wrong

```once
-- TYPE ERROR: Cata requires finite input (μ-type)
parseForever : Stream Char → Json
parseForever = Cata alg  -- Won't compile! Stream is ν-type, not μ-type

-- Instead, you must bound it:
parseBounded : Int → Stream Char → Maybe Json
parseBounded limit = parseJson ∘ obs limit
```

The type system enforces: you cannot fold an infinite stream. You must explicitly bound it with `obs`.

---

### 3. The Self-Healing Event Loop

#### The Problem Everyone Has

```python
# The game loop of doom
def game_loop():
    while running:
        events = poll_events()
        for event in events:
            handle_event(event)  # Might hang on weird input
        update_world()           # Might hang on edge case
        render()                 # Might hang on GPU stall
        # If ANY of these hang, your game freezes
```

Game developers know: one bad frame handler and your game is unresponsive. One infinite loop in physics and players Alt+F4.

#### The Once Way

```once
-- A game is a transformation: inputs → frames
game : Stream Input → Stream Frame

game = ana step initialWorld
  where
    step : World → (Frame, World)
    step world =
        let input = currentInput world
            world' = updatePhysics (handleInput input world)
            frame = render world'
        in (frame, world')
```

**Every step produces a frame.** Not "tries to produce" — WILL produce. If `updatePhysics` or `render` could hang, they wouldn't typecheck as total functions.

#### Handling Variable-Rate Events

```once
-- Events might come in bursts
-- Process all pending, but bound the batch
processEvents : Stream Event → Stream (List Effect)

processEvents = map processBatch ∘ buffer 16
  where
    processBatch : List Event → List Effect
    processBatch = concatMap handleEvent

    -- Buffer at most 16 events per frame
    buffer : Int → Stream Event → Stream (List Event)
    buffer n = map (obs n) ∘ chunk
```

The `buffer 16` ensures: no matter how many events flood in, you process at most 16 per frame. Bounded latency, guaranteed.

#### State Machines Made Safe

```once
-- Game states as a type
data GameState = Menu | Playing World | Paused World | GameOver Score

-- State machine as unfold
gameStateMachine : GameState → Stream Input → Stream Frame

gameStateMachine initial inputs = ana transition (initial, inputs)
  where
    transition : (GameState, Stream Input) → (Frame, (GameState, Stream Input))
    transition (state, inputs) =
        let input = head inputs
            (frame, state') = step state input
        in (frame, (state', tail inputs))

    step : GameState → Input → (Frame, GameState)
    step Menu input = case input of
        StartPressed → (playingFrame, Playing initialWorld)
        _ → (menuFrame, Menu)
    step (Playing world) input = case input of
        PausePressed → (pauseFrame world, Paused world)
        QuitPressed → (gameOverFrame 0, GameOver 0)
        _ → let world' = update world input
            in (renderWorld world', Playing world')
    -- ... etc
```

**Every state transition is explicit.** Every input in every state has a defined response. No "undefined behavior."

#### Why This Can't Go Wrong

```once
-- TYPE ERROR: update must be total
update : World → Input → World
update world input =
    if collision world
    then update world input  -- REJECTED: infinite loop!
    else move world input
```

The compiler rejects non-structural recursion. You can't accidentally write a physics update that loops forever on edge cases.

---

### 4. The Bounded Resource Pool

#### The Problem Everyone Has

```java
// The connection leak everyone's written
Connection conn = pool.acquire();
try {
    doWork(conn);
} finally {
    pool.release(conn);  // Hope you remembered this!
}

// Narrator: They did not remember.
```

Every language has tried to solve this:
- Java: try-with-resources (still easy to forget)
- Python: context managers (still easy to forget)
- Go: defer (still easy to forget)
- Rust: RAII (finally, but complex lifetimes)

#### The Once Way

```once
-- A connection has linear type (quantity = 1)
-- It MUST be used exactly once

withConnection : (Connection ⊸ IO Result) → IO Result
withConnection action = do
    conn ← acquire
    result ← action conn  -- conn is consumed here
    -- No release needed: conn was linear, action consumed it
    pure result
```

**The `⊸` is a linear arrow.** It means: the `Connection` must be used exactly once. Not zero times (leak), not twice (use-after-free). Exactly once.

```once
-- TYPE ERROR: connection not used
leaky : Connection ⊸ IO Unit
leaky conn = pure ()  -- Error: conn unused!

-- TYPE ERROR: connection used twice
double : Connection ⊸ IO Unit
double conn = do
    query conn "SELECT 1"
    query conn "SELECT 2"  -- Error: conn already used!

-- CORRECT: connection used exactly once
correct : Connection ⊸ IO Result
correct conn = query conn "SELECT * FROM users"
```

#### Resource Pools

```once
-- A pool manages N connections
-- Each checkout is linear
Pool : Type
checkout : Pool → IO (Connection ⊸ IO Unit → IO Unit)

-- Usage: the callback receives a linear connection
usePool : Pool → IO Result
usePool pool = do
    withConn ← checkout pool
    withConn (λ conn → query conn "SELECT 1")
```

The type of `checkout` is wild but precise: you get a function that takes a callback. The callback receives a linear connection. When the callback returns, the connection is automatically returned to the pool.

**You cannot forget to release.** The type system enforces it.

#### File Handles

```once
-- Same pattern for files
withFile : Path → (Handle ⊸ IO a) → IO a
withFile path action = do
    handle ← open path
    result ← action handle  -- handle consumed
    -- Automatically closed
    pure result

-- Cannot leak file handles
processFile : Path → IO (List Line)
processFile path = withFile path readAllLines
```

#### Why This Can't Go Wrong

Linear types make resource leaks a *compile error*, not a runtime bug:

```once
-- TYPE ERROR at compile time, not a leak at runtime
leakHandle : IO Unit
leakHandle = do
    handle ← open "data.txt"
    pure ()  -- Error: handle not used!

-- TYPE ERROR: can't escape the scope
escapeHandle : IO Handle
escapeHandle = withFile "data.txt" (λ h → pure h)  -- Error: h is linear!
```

#### Caveats

Linear types add real constraints:
- **Composition is harder** — you can't freely duplicate or discard linear values
- **APIs must be designed for linearity** — not all patterns translate cleanly
- **Learning curve** — thinking linearly takes practice

Once uses QTT (Quantitative Type Theory) which is more expressive than simple linear types, but there's still overhead. The tradeoff: more upfront thinking for guaranteed cleanup.

---

### 5. The Fused Pipeline

#### The Problem Everyone Has

```python
# Looks innocent...
result = (
    data
    .map(parse)        # Allocates new list
    .filter(valid)     # Allocates new list
    .map(transform)    # Allocates new list
    .reduce(combine)   # Finally produces result
)
# 3 intermediate lists, 4 passes over data
```

You've been told "don't worry, the compiler optimizes it." Sometimes it does. Sometimes it doesn't. You never quite know.

#### The Once Way

```once
-- Looks the same...
result : Summary
result =
    data
    |> map parse
    |> filter valid
    |> map transform
    |> fold combine empty
```

**But Once *guarantees* fusion.** The intermediate lists don't exist. This compiles to a single pass:

```once
-- What actually executes (conceptually):
result = fold (λ acc x →
    let parsed = parse x in
    if valid parsed
    then combine acc (transform parsed)
    else acc
  ) empty data
```

#### How Fusion Works

The secret is `Hylo`. When you compose `Cata` (fold) with `Ana` (unfold), they fuse:

```once
-- map is secretly an unfold-then-fold
map : (a → b) → List a → List b
map f = Cata (case Nil → Nil; Cons x xs → Cons (f x) xs)

-- filter is also an unfold-then-fold
filter : (a → Bool) → List a → List a
filter p = Cata (case Nil → Nil; Cons x xs → if p x then Cons x xs else xs)

-- When you compose them, they fuse into a single Hylo
-- No intermediate list is created
```

#### Seeing Fusion in Action

```once
-- Processing a stream of sensor data
pipeline : Stream Reading → Summary
pipeline =
    obs 1000                    -- Take 1000 readings
    ∘ filter (λ r → r.valid)    -- Keep valid ones
    ∘ map (λ r → r.value)       -- Extract values
    ∘ fold stats emptyStats     -- Compute statistics

-- This is ONE pass:
-- For each of 1000 readings:
--   If valid, update stats with value
-- No intermediate lists, no multiple traversals
```

#### The Fusion Guarantee

Once's fusion isn't "best effort" — it's structural:

| Pattern | Fuses To |
|---------|----------|
| `fold ∘ map` | Single `fold` |
| `fold ∘ filter ∘ map` | Single `fold` |
| `map ∘ map` | Single `map` |
| `fold ∘ obs n` | `Hylo` (no intermediate list) |

The `Hylo` primitive IS the fused form. When you write compositions that match these patterns, the optimizer doesn't need to be clever — the fusion is definitional.

#### Why This Works

The magic comes from how observation primitives are implemented:

```once
-- obs is a Hylo, not a Cata-then-Ana
obs : Nat → Stream a → List a
obs n stream = Hylo listAlg obsCoalg (n, stream)

-- So: fold (obs n stream) = fold (Hylo ...)
-- Which fuses to: Hylo foldAlg obsCoalg
-- Single pass, no intermediate list!
```

When you write `sum (obs 100 stream)`, it compiles to:
- Observe 100 elements
- Sum them as you go
- Never build a list

#### Limitations

Fusion in Once is structural, not magical:
- **Known patterns fuse** — Cata∘Ana, Hylo compositions, map∘map
- **Arbitrary compositions may not** — the optimizer isn't omniscient
- **Side effects break fusion** — effectful operations create sequencing points

The guarantee is: patterns that *should* fuse *do* fuse, by construction. But not every pipeline you write will collapse to a single pass.

---

## Part 2: Why This Works (Reference)

### 6. The Recursion Cheatsheet

**"I want to..."** → **"Use..."**

| Goal | Pattern | Example |
|------|---------|---------|
| Reduce a list to a value | `Cata` | `sum`, `length`, `all` |
| Transform each element | `Cata` (or `map`) | `map f list` |
| Filter elements | `Cata` | `filter p list` |
| Generate a list from seed | `Ana` | `range 1 10`, `replicate n x` |
| Generate infinite stream | `Ana` | `iterate f x`, `repeat x` |
| Take first n from stream | `obs n` | `obs 10 stream` |
| Take while condition | `obsWhile p` | `obsWhile (< 100) stream` |
| Transform and consume (fused) | `Hylo` | `factorial`, fused pipelines |
| Process with access to original | `Para` | `tails`, `safe tail` |
| Generate with early termination | `Apo` | `insertSorted` |

**Quick type reference:**

```once
Cata  : (F A → A) → μ F → A           -- Fold finite structure
Ana   : (A → F A) → A → ν F           -- Unfold to infinite structure
Hylo  : (F B → B) → (A → F A) → A → B -- Fused unfold-fold
obs   : Nat → ν F → μ F               -- Bound infinite to finite
```

**The μ/ν rule:**
- `μ` = finite (lists, trees, parsed data) → use `Cata` to consume
- `ν` = infinite (streams, event sources) → use `obs` to bound, then `Cata`

---

### 7. Types as Documentation

Reading Once types tells you a lot:

```once
-- "Always succeeds, returns a B"
f : A → B

-- "Might fail, returns Maybe B"
f : A → Maybe B

-- "Uses the A exactly once (linear)"
f : A ⊸ B

-- "Does IO, produces B"
f : A → IO B

-- "Transforms infinite stream to infinite stream"
f : Stream A → Stream B

-- "Consumes finite list, produces value"
f : List A → B

-- "Bounds infinite to finite"
f : Nat → Stream A → List A
```

**Type patterns and their meanings:**

| Type Pattern | Meaning |
|--------------|---------|
| `A → B` | Pure, total, always returns |
| `A → Maybe B` | Might fail |
| `A → Either E B` | Might fail with error info |
| `A ⊸ B` | Consumes A exactly once |
| `μ F → A` | Consumes finite structure |
| `A → ν F` | Produces (possibly infinite) structure |
| `ν F → μ F` | Bounds infinite to finite (uses `obs`) |
| `Stream A → Stream B` | Transforms infinite, element by element |

---

### 8. When Things Go Wrong

**Error: "Cannot unify μ-type with ν-type"**

You're trying to fold an infinite structure:
```once
-- BAD: List operations on Stream
length : Stream A → Nat  -- Error!

-- GOOD: Bound first
lengthOf100 : Stream A → Nat
lengthOf100 = length ∘ obs 100
```

**Error: "Linear variable not used"**

You have a resource you didn't consume:
```once
-- BAD: Connection leaked
bad conn = pure ()

-- GOOD: Use the connection
good conn = query conn "SELECT 1"
```

**Error: "Linear variable used multiple times"**

You're trying to use a resource twice:
```once
-- BAD: Double use
bad conn = (query conn "A", query conn "B")

-- GOOD: Sequence the uses
good conn = do
    a ← query conn "A"
    -- conn is gone now, can't use again
```

**Error: "Non-structural recursion"**

Your recursion doesn't make progress:
```once
-- BAD: Might loop forever
bad x = if condition then bad x else x

-- GOOD: Recurse on smaller structure
good list = case list of
    [] → ...
    (x :: xs) → ... good xs ...  -- xs is smaller than list
```

---

## Part 3: Going Deeper (Optional)

### 9. The Theory, If You're Curious

You don't need this section to use Once effectively. But if you want to understand *why* it works...

> **For the full categorical treatment:** See [Structured Recursion in Once: A Categorical Foundation](structured-recursion.md) — a deep dive for Haskellers familiar with `recursion-schemes` and category theorists who want the formal foundations.

#### Initial Algebras and Final Coalgebras

A `μ-type` is an **initial algebra**. Think of it as "the smallest type satisfying an equation":

```
List A = 1 + A × List A
       = Nil | Cons A (List A)
```

The "initial" means: there's exactly one way to fold it. That's `Cata`.

A `ν-type` is a **final coalgebra**. Think of it as "the largest type satisfying an equation":

```
Stream A = A × Stream A
         = (head, tail) forever
```

The "final" means: there's exactly one way to unfold into it. That's `Ana`.

#### Why μ ≠ ν Matters

In Haskell, `Fix f` unifies both. That's convenient but dangerous:

```haskell
-- Haskell: This typechecks but doesn't terminate
badSum :: Fix (ListF Int) → Int
badSum = cata alg where
    alg Nil = 0
    alg (Cons x xs) = x + xs

infiniteList :: Fix (ListF Int)
infiniteList = ana coalg 0 where
    coalg n = Cons n (n + 1)

boom = badSum infiniteList  -- Runs forever!
```

In Once, this is a **type error**:

```once
-- Once: Type error! Stream ≠ List
badSum : Stream Int → Int
badSum = Cata alg  -- Error: Cata needs μ-type, Stream is ν-type
```

The split forces you to be explicit about boundaries:

```once
-- Must bound the infinite:
goodSum : Nat → Stream Int → Int
goodSum n = sum ∘ obs n
```

#### Lambek's Lemma

Why can we pattern-match on recursive types? Lambek's Lemma (1968) says:

> For an initial algebra `In : F(μF) → μF`, the map `In` is an isomorphism.

This means `μF ≅ F(μF)`. A list IS either Nil or Cons. Not "represented by" — IS.

The inverse `out-μ : μF → F(μF)` lets us pattern-match. The isomorphism means pattern-matching is total: every value matches exactly one pattern.

#### Why Productivity is Free

In Once, `Ana` is always productive because:

1. Coalgebras are IR morphisms: `A → F(A)`
2. IR morphisms are total (no general recursion)
3. Therefore: each coalgebra call terminates and produces one `F`-layer
4. Therefore: `Ana` always makes progress

No guardedness checker needed. Productivity follows from totality.

#### The Hylo Fusion

`Hylo` is defined as:

```
hylo alg coalg x = alg (fmap (hylo alg coalg) (coalg x))
```

Conceptually "unfold then fold", but the intermediate structure never exists. It's the categorical composition of `Cata alg ∘ Ana coalg`, computed directly.

When you write `sum (obs n stream)`:
- `obs n` is a `Hylo` (unfold counter, fold into list)
- `sum` is a `Cata` (fold list into number)
- Composed: `Cata ∘ Hylo` fuses to a single `Hylo`
- Result: directly compute sum while observing, no list

This isn't optimization — it's how the operations are *defined*.

---

## Summary

**The Once Promise (for pure code):**

1. **Your pure handlers can't loop** — every function is total
2. **Your parser can't infinite-loop** — recursion is structural
3. **Your frame updates can't freeze** — every step completes
4. **Your resources can't leak** — linear types enforce cleanup
5. **Your pipelines fuse** — intermediate structures vanish

All of this is **enforced by the type system**, not by discipline or testing.

**What Once doesn't solve:**
- I/O operations can still block (waiting on network, disk, databases)
- External systems can still fail or hang
- The runtime itself is trusted (not formally verified)
- Concurrency bugs (data races) require additional care

**The effects story:** Effects compose orthogonally with recursion schemes. Use `Eff X Y` as the carrier type, sequence effects with `>>>`. The scheme handles structure; the algebra handles effects. No special primitives needed — just composition. See the [categorical deep dive](structured-recursion.md#effects-and-structured-recursion) for details.

**The key insight:** Once eliminates a large class of bugs — infinite loops, forgotten base cases, resource leaks, unfused pipelines — by making them type errors. It doesn't solve everything, but it solves enough to change how you think about correctness.

Welcome to programming where "it compiles" means more than it used to.
