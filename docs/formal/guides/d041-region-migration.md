# D041 Region Migration Guide

## Summary

This guide documents the D041 abstract region approach for memory preservation proofs in the x86 backend. The key insight is to model memory as three disjoint regions (Stack, Heap, Code) rather than using concrete addresses and arithmetic bounds.

## STOP RULE: Before Adding ANY Postulate

**If you cannot express something using the existing abstractions below, STOP and ASK.**

The likelihood of needing a new postulate is close to zero. If you think you need one, you are probably on the wrong path.

## Available Abstractions (MemoryRegions.agda)

### Inter-Region (stack vs heap vs code)

```agda
region-of : Addr → Region                    -- Each address has a region
regions-disjoint : r₁ ≢ r₂ → ...→ a₁ ≢ a₂   -- Different regions → different addresses
stack-code-disjoint : ...                    -- Stack ≢ Code
stack-heap-disjoint : ...                    -- Stack ≢ Heap
```

### Intra-Stack (caller frame vs current frame)

```agda
StackPointer : Set                           -- Abstract stack pointer (addr + in-stack proof)
slot-addr : StackPointer → ℕ → Addr          -- Slot at offset k from SP

-- KEY: These give intra-stack disjointness via StackPointer identity
sp-distinct : sp₁ ≢ sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k    -- Different SPs → different slots
offset-distinct : k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂  -- Different offsets → different slots
```

### How to Prove Memory Preservation

**For heap/code addresses:** Use `stack-code-disjoint` or `stack-heap-disjoint`

**For caller's stack addresses:**
- Caller has `caller-sp : StackPointer`
- Current frame has `current-sp : StackPointer`
- Prove `addr caller-sp ≢ addr current-sp`
- By `sp-distinct`: their slot addresses are different

## Forbidden Patterns

1. **No arithmetic comparisons at proof level**: `<`, `>`, `≤`, `≥`, `addr > rbp`
2. **No "middle" postulates**: Either use existing axioms or extend top-level (after asking)
3. **No abstract predicates like `InCallerRegion`**: Use `StackPointer` identity instead
4. **No "above/below" language**: Even in comments, this leads to arithmetic thinking
5. **No mentioning arithmetic even in negation**: Don't write "no arithmetic comparison" - just describe what IS done, not what ISN'T. Comments like "Uses sp-distinct (no arithmetic)" still plant arithmetic in the reader's mind.

## Correct Approach for Caller Memory Preservation

**WRONG (arithmetic):**
```agda
mem-caller : ∀ addr → addr > rbp → preserved
```

**RIGHT (StackPointer-based):**
```agda
-- Caller passes their StackPointer
-- Current frame has its own StackPointer
-- Disjointness follows from sp-distinct
mem-caller : ∀ caller-sp current-sp → addr caller-sp ≢ addr current-sp → preserved
```

## CRITICAL PRINCIPLE: Purely Region-Based Proofs

The D041 approach uses **only region membership and disjointness**:

1. **Region Membership**: Prove addresses belong to regions (stack, heap, code)
2. **Region Disjointness**: Use `stack-code-disjoint`, `stack-heap-disjoint`
3. **Intra-Stack Disjointness**: Use `sp-distinct`, `offset-distinct`
4. **Memory Preservation**: `readMem-writeMem-diff` with inequality from above

## Available Infrastructure (StackInvariant2.agda)

**Key Proven Lemmas:**
- `stack-write-preserves-r15` - Universal lemma handling all R15Status cases
- `stack-write-preserves-zero-r15` - Stack writes don't affect address 0
- `stack-write-preserves-code-r15` - Stack writes don't affect code region
- `stack-write-preserves-heap-data` - Stack writes don't affect heap data
- `capacity-maintained` - Proves addresses at `rsp - k*8` are in stack region

**Global Axioms (in MemoryRegions.agda):**
- `regions-disjoint` - Foundational region separation
- `sp-distinct` - Different SPs → different addresses
- `offset-distinct` - Different offsets → different addresses

## Pre-Commit Checklist

- [ ] All execution proofs use `Star` composition
- [ ] Memory preservation via region proofs
- [ ] Caller memory via `sp-distinct`
- [ ] No new local postulates
- [ ] No "above/below" language in comments

## Verification

```bash
cd formal
make -j8 x86-ccc  # Full x86 backend type-check
```
