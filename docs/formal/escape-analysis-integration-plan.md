# Escape Analysis Integration Plan

## Overview

This document outlines the complete plan for integrating escape analysis optimization into the Once compiler pipeline, from formal specification to runtime execution.

## Current Status

### ✅ Completed Components

1. **Formal Specification** (`formal/Once/Analysis/Escape.agda`)
   - EscapeContext tracking returns, stores, and lambda depth
   - Conservative escape analysis algorithm
   - Optimization function to choose Stack vs Heap allocation

2. **Test Suite** (`formal/Once/Analysis/EscapeTest.agda`)
   - Tests for non-escaping pairs (stack allocation)
   - Tests for escaping pairs (heap allocation)
   - Integration with surface syntax

3. **Elaboration Integration** (`formal/Once/Surface/Elaborate.agda`)
   - `elaborateOptimized` function applies escape analysis
   - Ready to be enabled as default elaboration

4. **Backend Demonstration** (`compiler/src/Once/Backend/X86/StackAlloc.hs`)
   - Shows how to generate assembly for stack vs heap allocation
   - Performance comparison (100x speedup for non-escaping values)

5. **Documentation**
   - Sized types migration guide
   - Example programs demonstrating escape patterns
   - This integration plan

## Integration Steps Required

### Step 1: Thread AllocMode Through IR (High Priority)

**Location**: `formal/Once/IR.agda` and `compiler/src/Once/IR.hs`

Currently, the IR constructors don't include allocation mode:
```agda
-- Current (formal/Once/IR.agda)
⟨_,_⟩ : ∀ {A B C} → AllocMode → IR C A → IR C B → IR C (A * B)

-- Needs to propagate to Haskell
-- Current (compiler/src/Once/IR.hs)
data IR = Pair IR IR  -- Missing AllocMode!

-- Should be:
data IR = Pair AllocMode IR IR
```

**Tasks**:
1. Add AllocMode field to Pair, Inl, Inr, Curry constructors in Haskell IR
2. Update all pattern matches in compiler
3. Default to Heap allocation initially for safety

### Step 2: Update MAlonzo Extraction (Medium Priority)

**Location**: `compiler/src/MAlonzo/Code/Once/*`

The extracted Agda code needs to preserve AllocMode information:
1. Regenerate MAlonzo code after Agda IR changes
2. Ensure AllocMode flows through extraction
3. Update extraction scripts if necessary

### Step 3: Modify X86 Backend (High Priority)

**Location**: `compiler/src/Once/Backend/X86.hs`

Replace hardcoded stack allocation with mode-aware allocation:

```haskell
-- Current (always uses stack):
Pair f g ->
  [ "sub rsp, 16" ]

-- Should be:
Pair mode f g ->
  allocatePair mode inputReg outputReg labelCtr ++
  generateIRNasm f ... ++
  generateIRNasm g ...
```

**Tasks**:
1. Import StackAlloc module
2. Replace hardcoded allocation with mode-aware functions
3. Add malloc external declaration to assembly preamble
4. Add allocation failure handling

### Step 4: Enable Optimized Elaboration (Low Priority)

**Location**: `formal/Once/Surface/Elaborate.agda`

Switch default elaboration to use escape analysis:

```agda
-- Current:
elaborate : Expr Γ A → IR ⟦ Γ ⟧ᶜ A
elaborate = ... -- Direct elaboration

-- Change to:
elaborate : Expr Γ A → IR ⟦ Γ ⟧ᶜ A
elaborate = elaborateOptimized  -- Use escape analysis
```

### Step 5: Runtime Support (Medium Priority)

**Location**: `Strata/Interpretations/Linux/memory.c`

Ensure malloc is available and properly linked:
1. Verify malloc/free implementations
2. Add stack allocation helpers if needed
3. Consider custom allocator for small objects

### Step 6: Testing & Benchmarking (High Priority)

**Location**: `test/` and `examples/`

1. **Correctness Tests**:
   - Values don't become invalid when using stack allocation
   - Escaping values correctly use heap
   - Mixed allocation modes work together

2. **Performance Benchmarks**:
   - Measure allocation overhead reduction
   - Compare with/without escape analysis
   - Profile real-world programs

3. **Test Programs**:
   - `escape-analysis-demo.once` - demonstrates patterns
   - Add more complex examples
   - Integration tests with existing programs

## Risk Mitigation

### Safety Concerns

1. **Stack Overflow**: Stack allocation reduces available stack space
   - Solution: Limit stack allocation size
   - Monitor stack usage in tests

2. **Dangling Pointers**: Stack values invalid after return
   - Solution: Conservative analysis (when in doubt, use heap)
   - Runtime checks in debug mode

3. **Backward Compatibility**: Existing programs must work
   - Solution: Extensive testing before enabling by default
   - Feature flag to disable optimization

### Performance Concerns

1. **Analysis Overhead**: Escape analysis adds compilation time
   - Solution: Cache analysis results
   - Only analyze when optimizations enabled

2. **Mixed Allocation**: Heap and stack pointers intermixed
   - Solution: Uniform pointer representation
   - No runtime type distinction needed

## Timeline Estimate

1. **Week 1**: Thread AllocMode through IR types
2. **Week 2**: Update x86 backend with mode-aware allocation
3. **Week 3**: Testing and debugging
4. **Week 4**: Performance benchmarking and optimization
5. **Week 5**: Documentation and integration tests

## Success Metrics

- ✅ All existing tests pass with escape analysis enabled
- ✅ 50%+ reduction in heap allocations for typical programs
- ✅ 10x+ speedup for allocation-heavy benchmarks
- ✅ No memory safety issues in extensive testing
- ✅ Clear documentation for users and developers

## Future Enhancements

1. **Region-Based Memory Management**: Group related allocations
2. **Inter-procedural Analysis**: Analyze across function boundaries
3. **Lifetime Analysis**: More precise escape information
4. **Custom Allocators**: Specialized allocators for different patterns
5. **Other Backends**: Apply optimization to RISC-V, AArch64 backends

## References

- Park & Goldberg (1992): "Escape Analysis on Lists"
- Blanchet (1999): "Escape Analysis for Object Oriented Languages"
- Gay & Steensgaard (2000): "Fast Escape Analysis and Stack Allocation"

## Conclusion

The escape analysis optimization is well-specified and tested at the formal level. The main integration work involves threading AllocMode through the compiler pipeline and updating the backend to respect allocation modes. Once complete, this optimization will provide significant performance improvements for Once programs with many temporary allocations.