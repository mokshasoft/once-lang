# Stack Optimization Strategies for Once

## Problem Statement

The fannkuch benchmark crashes with stack overflow for n≥8 due to deep recursion without tail-call optimization. The generated C code uses direct recursive calls that gcc cannot optimize into loops.

**Root cause**: `fannkuchLoop` makes 40,320 recursive calls for n=8, each consuming ~200-400 bytes of stack.

## Design Constraint: Orthogonality to Generators

Any solution must be **orthogonal to code generators**. Once targets multiple backends:
- C (current)
- RISC-V assembly
- AArch64 assembly
- x86-64 assembly
- Potentially: WASM, LLVM IR

The optimization should happen at a level where all backends benefit, not be reimplemented per-backend.

## Option 1: Tail-Call Detection + Loop Transformation in IR

**Where**: IR → IR transformation pass (before codegen)

**How**: Detect tail-recursive functions and transform them to use an explicit loop construct in the IR.

```
-- Before (IR)
f : A → B
f = ... case ... { Left → ...; Right → f(x) }

-- After (IR)
f : A → B
f = loop (\x → ... case ... { Left → break(...); Right → continue(x) })
```

**Pros**:
- All backends benefit automatically
- Clean separation of concerns
- Preserves Once's categorical semantics at source level

**Cons**:
- Need to add loop/break/continue to IR (Once currently has no loops)
- Tail-call detection is non-trivial for mutual recursion
- May complicate formal verification (IR semantics change)

**Tail-call criteria**:
1. Recursive call is the last operation before return
2. No work done after the call (no composition `g ∘ f` where f is recursive)
3. Return type matches without wrapping

## Option 2: CPS Transformation in Compiler

**Where**: Surface → IR elaboration, or IR → IR pass

**How**: Transform all functions to continuation-passing style internally.

```haskell
-- Source
f : A → B
f = \x → case g(x) of { Left a → h(a); Right b → f(b) }

-- CPS-transformed (internal)
f_cps : A → (B → R) → R
f_cps = \x → \k → case g(x) of { Left a → k(h(a)); Right b → f_cps(b, k) }
```

Then codegen emits a trampoline:
```c
while (1) {
    result = step(&state);
    if (result.done) return result.value;
    state = result.next_state;
}
```

**Pros**:
- All recursion becomes tail recursion
- Programmer writes natural recursive code
- Enables other optimizations (delimited continuations, async)

**Cons**:
- **Closure allocation**: CPS creates many continuations (closures)
- **Memory pressure**: Trades stack for heap
- **Debugging**: Stack traces become meaningless
- **Interaction with linearity**: Continuations are typically used once (affine), but CPS may require careful handling with QTT
- **Code size**: Every function gets a continuation parameter

**CPS + Defunctionalization** (to avoid closures):
Convert continuations to a data type, then interpret:
```haskell
data Cont = Done | KThen Cont | KElse Cont | ...

apply : Cont → Value → Value
apply Done v = v
apply (KThen k) v = apply k (then_body v)
```

This avoids heap-allocated closures but requires whole-program analysis.

## Option 3: Leverage Linearity (QTT) for In-Place Updates

**Where**: Type system + codegen

**How**: Once's QTT tracks resource usage. Linear values (used exactly once) can be updated in-place. This doesn't directly solve stack overflow but reduces allocation overhead.

For tail recursion specifically: if the recursive call consumes the only reference to state, the state can be mutated in place:

```
-- Linear state threading
loop : S ⊸ S  -- S used linearly
loop = \s → case done(s) of {
    Left result → result;
    Right s' → loop(s')  -- s' is the only reference
}
```

**Codegen insight**: When the recursive call is:
1. In tail position
2. The argument is linear (no other references)
3. Same type as input

Then codegen can emit:
```c
while (1) {
    if (done(state)) return result;
    state = next(state);  // in-place update
}
```

**Pros**:
- Natural fit with Once's design
- No new IR constructs needed
- Formal verification friendly (linearity is already proven)

**Cons**:
- Only works for linear state
- Requires tail-position detection
- Need to verify linearity at the point of recursion

## Option 4: Trampoline Pattern in Codegen

**Where**: Codegen only (per-backend, but simple)

**How**: Detect recursive functions and emit trampoline wrappers.

```c
// Instead of:
OncePair f(OncePair x) {
    ...
    return f(next_x);  // stack grows
}

// Emit:
typedef struct { int tag; OncePair value; } Thunk;
#define DONE(v) ((Thunk){0, v})
#define CALL(v) ((Thunk){1, v})

Thunk f_step(OncePair x) {
    ...
    return CALL(next_x);  // returns instead of calling
}

OncePair f(OncePair x) {
    Thunk t = f_step(x);
    while (t.tag == 1) {
        t = f_step(t.value);
    }
    return t.value;
}
```

**Pros**:
- Simple to implement
- No IR changes
- Works with existing semantics

**Cons**:
- Must be implemented per-backend (not orthogonal)
- Adds overhead for non-recursive functions if applied universally
- Mutual recursion requires more complex dispatch

## Option 5: Stack Frames on Heap (Stackless)

**Where**: Codegen

**How**: Allocate activation records on heap instead of stack.

```c
typedef struct Frame {
    struct Frame* parent;
    int pc;  // program counter within function
    // locals...
} Frame;

void* interpret(Frame* f) {
    while (f) {
        switch (f->pc) {
            case 0: /* first statement */ ...
            case 1: /* recursive call */
                f = new_frame(f, args);
                continue;
            case 2: /* after return */
                f = f->parent;
                continue;
        }
    }
}
```

**Pros**:
- Unlimited "recursion" depth
- Enables coroutines, green threads

**Cons**:
- Significant codegen complexity
- Performance overhead
- Not orthogonal (each backend needs this)
- Essentially building a VM

## Option 6: Detect Loop Patterns at Surface Level

**Where**: Parser/Elaborator

**How**: Recognize common iteration patterns and elaborate to efficient IR.

```
-- Surface: looks recursive
sum : List Int → Int
sum = \xs → case xs of {
    Nil → 0;
    Cons x xs' → x + sum(xs')
}

-- Detected pattern: fold
-- Elaborate to primitive fold operation
sum = fold (+) 0
```

**Pros**:
- High-level optimization
- Could enable fusion, parallelization

**Cons**:
- Limited to recognized patterns
- Doesn't help general recursion
- Complex pattern matching in compiler

## Recommendation

### Short-term: Option 4 (Trampoline in Codegen)

Implement trampolines for the C backend specifically. This unblocks benchmarks quickly.

Detection criteria for trampolining:
1. Function calls itself (direct recursion)
2. Recursive call is in tail position
3. No mutual recursion (initially)

### Medium-term: Option 1 + 3 (IR Loop Transform + Linearity)

Add a tail-call analysis pass that:
1. Detects tail-recursive functions
2. Checks if state is linear
3. Transforms to explicit loop in IR

This is orthogonal to backends and leverages Once's type system.

### Long-term: Option 2 (Selective CPS)

For complex control flow (mutual recursion, early exit), implement CPS transformation with defunctionalization. This is the most general solution but requires careful design.

## Implementation Phases

### Phase 1: Tail-Call Detection
Add analysis pass to identify tail-recursive functions:
```haskell
-- In compiler
isTailRecursive :: Decl → Bool
isTailRecursive decl =
    let calls = findRecursiveCalls (body decl)
    in all isInTailPosition calls
```

### Phase 2: Loop IR Construct
Extend IR with loop primitive:
```haskell
data IR a b where
    ...
    Loop :: IR (a, s) (Either b s) → IR (a, s) b
```

Semantics: `Loop body` repeatedly applies `body` until it returns `Left b`.

### Phase 3: Transformation Pass
```haskell
transformTailRec :: Decl → Decl
transformTailRec decl
    | isTailRecursive decl = convertToLoop decl
    | otherwise = decl
```

### Phase 4: Codegen
All backends emit loops for the Loop IR construct:
```c
// C backend
while (1) {
    result = body(state);
    if (result.tag == 0) return result.value;
    state = result.value;
}
```

```asm
# RISC-V backend
.loop:
    call body
    beq a0, zero, .done
    mv a1, a0
    j .loop
.done:
```

## Questions to Resolve

1. **Mutual recursion**: How to handle `f` calls `g` calls `f`? Options:
   - Defunctionalize to single function with tag
   - Trampoline with function pointer
   - Don't optimize (rare in practice)

2. **Partial tail calls**: What if only some branches are tail-recursive?
   - Could split into loop + non-loop parts
   - Or only optimize fully tail-recursive functions

3. **Verification**: How does Loop affect formal proofs?
   - Loop has clear denotational semantics (least fixpoint)
   - May need to extend Agda formalization

4. **Interaction with effects**: Do effectful loops need special handling?
   - Probably not if effects are already in Eff monad
   - Loop body type: `IR (a, s) (Eff (Either b s))`

## References

- [Compiling with Continuations](https://www.cambridge.org/core/books/compiling-with-continuations/...) - CPS compilation
- [Defunctionalization at Work](https://www.brics.dk/RS/01/23/BRICS-RS-01-23.pdf) - Removing closures from CPS
- [Destination-Passing Style](https://www.microsoft.com/en-us/research/publication/...) - Linear types + efficient codegen
- Once QTT formalization in `formal/` - Linearity proofs
