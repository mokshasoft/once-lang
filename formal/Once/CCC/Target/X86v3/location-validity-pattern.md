# Location-Based Validity Pattern

## Problem

The untyped simulation layer (WholeProgram) needs validity proofs for operations
that read compound types from memory (fst, snd, apply, case, etc.).

Naive approaches fail:
- **"All states valid"** - Unsound. Arbitrary states don't have valid structure.
- **Existentially hidden** - Hides information the caller already has, complicates proofs.

## Insight

The caller (Dispatcher with ValidAtWF) already knows:
1. The **location** where the value lives (`pair-loc`, `closure-loc`, etc.)
2. The **structure** at that location (component pointers)
3. The **calling convention** (RDI points to input location)

The cleanest interface passes this information **explicitly**, not hidden.

## The Pattern

For each compound type, define a record that captures:
1. The root location (passed as parameter, not existentially quantified)
2. Component locations (fields)
3. Calling convention proof (rdi-eq for input, rax-eq for output)
4. Memory structure proofs (component pointers readable)

```agda
record <Type>AtLoc (loc : ValueLocation FS) (σ : LocState FS) : Set where
  field
    <component>-loc : ValueLocation FS           -- where components live
    rdi-eq : readReg (regs σ) RDI ≡ loc          -- calling convention
    <component>-ptr : readLoc σ <offset> ≡ ...   -- memory readable
```

## Instances

### Pairs (for fst-ir, snd-ir)

```agda
record PairAtLoc (pair-loc : ValueLocation FS) (σ : LocState FS) : Set where
  field
    fst-loc : ValueLocation FS
    snd-loc : ValueLocation FS
    rdi-eq : readReg (regs σ) RDI ≡ pair-loc
    fst-ptr : readLoc σ pair-loc ≡ just fst-loc
    snd-ptr : readLoc σ (sucLoc pair-loc) ≡ just snd-loc
```

### Closures (for apply)

```agda
record ClosureAtLoc (closure-loc : ValueLocation FS) (σ : LocState FS) : Set where
  field
    env-loc : ValueLocation FS
    code-loc : ValueLocation FS
    rdi-eq : readReg (regs σ) RDI ≡ closure-loc
    env-ptr : readLoc σ closure-loc ≡ just env-loc
    code-ptr : readLoc σ (sucLoc closure-loc) ≡ just code-loc
```

### Sums (for case-ir)

```agda
record SumAtLoc (sum-loc : ValueLocation FS) (σ : LocState FS) : Set where
  field
    payload-loc : ValueLocation FS
    rdi-eq : readReg (regs σ) RDI ≡ sum-loc
    payload-ptr : readLoc σ (sucLoc sum-loc) ≡ just payload-loc
    -- Note: tag is a value at sum-loc, not a pointer
```

### Recursive Types (for unfold-ir)

```agda
record FixAtLoc (fix-loc : ValueLocation FS) (σ : LocState FS) : Set where
  field
    unfolded-loc : ValueLocation FS
    rdi-eq : readReg (regs σ) RDI ≡ fix-loc
    unfolded-ptr : readLoc σ fix-loc ≡ just unfolded-loc
```

## Connection to Typed Layer

The Dispatcher has `ValidAtWF` which decomposes via:
- `decomposePairWF` → `PairValidWF` (fst-ptr, snd-ptr, component validity)
- `decomposeClosureWF` → `ClosureValidWF` (env-ptr, code-ptr, body proof)
- `decomposeInlWF` / `decomposeInrWF` → `InlValidWF` / `InrValidWF`

These typed decompositions contain exactly what `<Type>AtLoc` needs, plus:
- Semantic value (`⟦ A ⟧`) - not needed at untyped layer
- Allocation mode - not needed at untyped layer
- Component validity - recursive, for nested structures

The Dispatcher constructs `<Type>AtLoc` from:
1. `decompose<Type>WF` → component locations and pointers
2. Calling convention → `rdi-eq`

## Benefits

1. **Sound** - No false claims about arbitrary states
2. **Explicit** - All information named, not hidden in existentials
3. **Portable** - Works for any backend that uses the calling convention
4. **Uniform** - Same pattern for all compound types
5. **Easy to construct** - Matches what Dispatcher already has
6. **Easy to use** - Direct field access, no projection through existentials

## Output Validity

For operations that produce compound types (pair construction, curry, inl/inr),
use the same pattern with `rax-eq` instead of `rdi-eq`:

```agda
record PairOutputAtLoc (pair-loc : ValueLocation FS) (σ : LocState FS) : Set where
  field
    fst-loc : ValueLocation FS
    snd-loc : ValueLocation FS
    rax-eq : readReg (regs σ) RAX ≡ pair-loc
    fst-ptr : readLoc σ pair-loc ≡ just fst-loc
    snd-ptr : readLoc σ (sucLoc pair-loc) ≡ just snd-loc
```

This enables chaining: output validity of `f` becomes input validity of `g`
after the bridge instruction (`mov rdi, rax`).
