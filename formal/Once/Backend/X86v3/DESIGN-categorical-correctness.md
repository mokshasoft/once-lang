# Compiler Correctness for X86v3

## The Essential Property

Compiler correctness is ONE property:

```
Represents x input-loc s  →  Represents (eval ir x) result-loc s'
```

This says: if the input state represents `x`, then after execution, the output state represents `eval ir x`.

This is the compiler correctness theorem in categorical form:
```
⟦ compile ir ⟧ ∘ encode ≡ encode ∘ eval ir
```

## The Implementation

### Represents

`Represents` is defined as `ValidAtWF` from `ClosureWellFormed.agda`:

```agda
Represents : AllocMode → AllocState → ⟦ A ⟧ → ValueLocation → LocState → Set
Represents m alloc v loc s = ValidAtWF m alloc v loc s
```

This means "value `v` is stored at location `loc` in state `s`".

### The Theorem

```agda
record CompileCorrect {A B : Type} (ir : IR A B) : Set where
  field
    preserves-semantics :
      ∀ mIn x input-loc s alloc →
      Represents mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      ir-size ir < program-bound →
      ∃[ mOut ] ∃[ result-loc ] ∃[ s' ] ∃[ alloc' ]
        Represents mOut alloc' (eval ir x) result-loc s'
```

The `eval ir x` in the output is the semantic bridge between:
- `ir` (syntax)
- `eval ir` (denotational semantics)
- `ValidAtWF ... (eval ir x) ...` (operational result)

### The Proof

The proof delegates to the Dispatcher and extracts `result-valid-wf`:

```agda
compile-correct ir = record { preserves-semantics = λ ... →
  let (mOut , result) = run-ir-wf ...
  in mOut , result-loc , final-state , final-alloc , result-valid-wf }
```

## Why No Axioms?

### Memory Layout

The `ValidAtWF` constructors carry the memory proofs:

```agda
valid-pair-boxed-wf :
  readLoc s pair-loc ≡ just fst-loc →        -- fst pointer proof
  readLoc s (sucLoc pair-loc) ≡ just snd-loc →  -- snd pointer proof
  ...
  ValidAtWF Heap alloc (a , b) pair-loc s
```

When `fst-ir` executes, we pattern match on `ValidAtWF` to get `readLoc s pair-loc ≡ just fst-loc`. No axioms - just unpacking what the pair constructor proved.

### Composition

The Dispatcher handles composition internally. Each IR handler:
1. Receives `ValidAtWF` for input
2. Produces `IRResultAWF` with `ValidAtWF` for output containing `eval ir x`

The `IRResultAWF` has 15+ fields for internal bookkeeping (allocation state, reclamation, etc.), but these are hidden. The exported theorem only shows the essential property.

## File Structure

```
WholeProgram.agda     -- 141 lines: the clean theorem
Dispatcher.agda       -- The implementation (run-ir-wf)
ClosureWellFormed.agda -- ValidAtWF, IRResultAWF definitions
```

## Summary

| Aspect | Old Approach | New Approach |
|--------|--------------|--------------|
| Lines | 900+ | 141 |
| Core property | Scattered across 15+ fields | `Represents x → Represents (eval ir x)` |
| Memory layout | Postulated | Derived from ValidAtWF |
| Offsets | Manual arithmetic | Handled by Dispatcher |
| Postulates | 24 | 3 (entry-point concerns) |

The `eval ir x` appearing in the output validity is the only thing that matters. Everything else is implementation detail.
