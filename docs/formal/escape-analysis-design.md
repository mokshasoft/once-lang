# Escape Analysis Design for Once Language

## Overview

Escape analysis is an optimization technique that determines whether values "escape" their defining scope. Values that don't escape can be allocated on the stack (faster) instead of the heap (slower).

## Implementation Status

### Phase 1: Infrastructure (✅ Complete)
- Added `AllocMode` type to IR with `Stack` and `Heap` modes
- Modified IR constructors to include allocation mode parameters
- Added `pair` builtin for testing allocation patterns

### Phase 2: Formal Specification (✅ Complete)
- Created `Once.Analysis.Escape` module with escape analysis algorithm
- Defined escape contexts and analysis rules
- Removed deprecated sized types from formal proofs
- All formal proofs compile successfully

### Phase 3: Integration (🚧 In Progress)
- Created formal specification of escape analysis
- Next: Integrate with elaboration pipeline
- Next: Update code generation to use stack allocation

## Technical Design

### Escape Context

The analysis tracks three key properties:
1. **returns** - Will this value be returned from a function?
2. **stores** - Will this value be stored in a data structure?
3. **lambdaDepth** - Current lambda nesting depth (for closure captures)

### Analysis Rules

Values escape when they:
- Are returned from functions
- Are stored in data structures (pairs, sums)
- Are captured by closures (curry)
- Flow through recursive types (Fix)

Values don't escape when they:
- Are used locally and discarded
- Flow through projections (fst, snd)
- Are consumed by case analysis

### Optimization Strategy

The `optimizeAllocations` function:
1. Recursively analyzes each IR term
2. Determines escape status using conservative analysis
3. Chooses `Stack` allocation when safe, `Heap` otherwise

## Example

```agda
-- Non-escaping pair (can use stack)
example-local-pair : IR (Int * Int) Int
example-local-pair = fst  -- Pair consumed locally

-- Escaping pair (must use heap)
example-make-pair : IR Int (Int * Int)
example-make-pair = ⟨ id , id ⟩ Heap  -- Pair returned
```

## Files Modified

### Core Infrastructure
- `formal/Once/IR.agda` - Added AllocMode type
- `formal/Once/Analysis/Escape.agda` - Escape analysis implementation

### Type System
- `formal/Once/TypeSystem/Soundness.agda` - Removed sized types
- `formal/Once/TypeSystem/Typing.agda` - Removed sized types
- `formal/Once/Surface/Semantics.agda` - Surface semantics

### Type Checking
- `formal/Once/TypeCheck/Elaborate.agda` - Added pair builtin

### Backend
- `formal/Once/Backend/X86/Correct.agda` - Fixed curry application

### Documentation
- `docs/formal/guides/agda-sized-types-migration.md` - Migration guide
- `docs/formal/escape-analysis-design.md` - This document

## Testing

Created test infrastructure:
- `test/once-programs/allocation-test.once` - Test programs
- `test/AllocationSpec.hs` - Test specification

## Future Work

1. **Complete Integration**
   - Hook escape analysis into elaboration pipeline
   - Update x86 backend to emit stack allocations

2. **Advanced Analysis**
   - Inter-procedural escape analysis
   - Region-based memory management
   - Escape analysis for recursive types

3. **Performance Validation**
   - Benchmark stack vs heap allocation
   - Measure compilation time impact
   - Profile real-world programs

## Benefits

- **Performance**: Stack allocation is faster than heap
- **Memory**: Reduced heap pressure and GC overhead
- **Cache**: Better locality for stack-allocated data
- **Predictability**: More deterministic performance

## References

- Park & Goldberg (1992): "Escape Analysis on Lists"
- Blanchet (1999): "Escape Analysis for Object Oriented Languages"
- Gay & Steensgaard (2000): "Fast Escape Analysis and Stack Allocation"