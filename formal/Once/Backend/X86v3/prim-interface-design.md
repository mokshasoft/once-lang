# X86v3 Prim Interface Design

## Overview

Design the Prim interface for X86v3 using the SlotMachine model (slots, not addresses).

## Current State

```agda
-- IR.agda
Prim : ∀ {A B} → String → IR A B

-- Postulated
prim-semantics : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

-- Dispatcher.agda
postulate
  run-prim : ∀ {A B} (mIn : AllocMode) (name : String)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mOut ] IRResultAWF mOut (Prim name) x s alloc
```

## Target Design

### 1. PrimContractV3

The contract specifies what a primitive needs and produces:

```agda
record PrimContractV3 (A B : Type) : Set where
  field
    -- Stack slots required for execution
    stack-requirement : ℕ

    -- Output allocation mode (Stack = unboxed, Heap = boxed)
    output-mode : AllocMode
```

Note: No assembly needed - SlotMachine is symbolic execution.

### 2. IR Definition Change

Embed semantics directly in constructor (like X86):

```agda
-- IR.agda
Prim : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) → PrimContractV3 A B → IR A B

-- Semantics is now definitional:
eval (Prim name sem c) x = sem x  -- No postulate needed!
```

### 3. PrimProofV3

What a correctness proof for a primitive must provide:

```agda
PrimProofV3 : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (c : PrimContractV3 A B) → Set
PrimProofV3 {A} {B} sem c =
  ∀ (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    -- Preconditions
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc + stack-requirement c ≤ frame-capacity alloc →
    -- Postcondition: IRResultAWF with output-mode from contract
    IRResultAWF (output-mode c) (Prim _ sem c) x s alloc
```

### 4. PrimProofProviderV3

Interface for domain compilers:

```agda
PrimProofProviderV3 : Set₁
PrimProofProviderV3 = ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (c : PrimContractV3 A B) →
  PrimProofV3 sem c
```

### 5. Dispatcher Changes

Parameterize by proof provider:

```agda
module Dispatcher {FS : FrameSemantics}
  (program-bound : ℕ)
  (acc-pb : Acc _<_ program-bound)
  ...existing params...
  (prim-proof : PrimProofProviderV3)  -- NEW
  where

  -- No postulate! Uses proof provider:
  run-prim : ∀ {A B} (mIn : AllocMode) (name : String)
    (sem : ⟦ A ⟧ → ⟦ B ⟧) (c : PrimContractV3 A B)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc + stack-requirement c ≤ frame-capacity alloc →
    IRResultAWF (output-mode c) (Prim name sem c) x s alloc
  run-prim mIn name sem c x input-loc s alloc valid bf nh rdi cap =
    prim-proof sem c mIn x input-loc s alloc valid bf nh rdi cap
```

## IRResultAWF Requirements

A Prim proof must produce all fields of IRResultAWF:

```agda
record IRResultAWF (mOut : AllocMode) (ir : IR A B) (x : ⟦ A ⟧)
       (s : LocState FS) (alloc : AllocState {FS}) : Set where
  field
    result-loc : ValueLocation FS
    final-state : LocState FS
    final-alloc : AllocState {FS}
    result-valid-wf : ValidAtWF mOut final-alloc (eval ir x) result-loc final-state
    result-before : BeforeFrontier final-alloc result-loc
    rax-is-result : readReg (regs final-state) RAX ≡ result-loc
    not-halted : halted final-state ≡ false
    frame-preserved : current-frame final-alloc ≡ current-frame alloc
    slot-monotone : next-slot alloc ≤ next-slot final-alloc
    heap-monotone : next-heap-ref alloc ≤ next-heap-ref final-alloc
    heap-preserved : heap final-alloc ≡ heap alloc  -- or similar
    capacity-preserved : frame-capacity final-alloc ≡ frame-capacity alloc
    mem-preserved-before : ∀ loc → BeforeFrontier alloc loc →
      readLoc final-state loc ≡ readLoc s loc
    -- Reclamation fields...
```

## Domain Compiler Example (Arith)

```agda
module ArithPrimProofs where
  -- Contract for integer addition
  add-int-contract : PrimContractV3 (Int * Int) Int
  add-int-contract = record
    { stack-requirement = 0  -- No stack needed
    ; output-mode = Stack    -- Result is unboxed
    }

  -- Semantics
  add-int-sem : ⟦ Int * Int ⟧ → ⟦ Int ⟧
  add-int-sem (a , b) = a + b

  -- Proof
  add-int-proof : PrimProofV3 add-int-sem add-int-contract
  add-int-proof mIn x input-loc s alloc valid bf nh rdi cap =
    record
      { result-loc = ...
      ; final-state = ...
      ; final-alloc = alloc  -- No allocation change
      ; result-valid-wf = ...  -- Construct ValidAtWF for result
      ; result-before = ...
      ; ...
      }
```

## Key Differences from X86

| Aspect | X86 | X86v3 |
|--------|-----|-------|
| Memory model | Addresses (ℕ) | Slots (ValueLocation) |
| Validity | ValidAt x addr mem | ValidAtWF m alloc x loc s |
| Contract | Assembly + nonempty | stack-requirement + output-mode |
| Proof type | Star trace | IRResultAWF |
| Assembly | Required | Not needed (symbolic) |

## Implementation Steps

1. **PrimContractV3 in IR.agda** ✓
   - Defined PrimContractV3 record with stack-requirement, output-mode, stack-req-bounded
   - PrimProofV3 and PrimProofProviderV3 defined in Dispatcher.agda (Set level, not Set₁)

2. **Update IR.agda** ✓
   - Changed Prim constructor to embed semantics and contract: `Prim name sem c`
   - Removed prim-semantics postulate
   - Updated eval: `eval (Prim _ sem _) x = sem x`

3. **Update Dispatcher.agda** ✓
   - Added prim-proof parameter via PrimProofProviderV3
   - Replaced run-prim postulate with proof invocation

4. **Update WholeProgram.agda** ✓
   - Added PrimProofProviderV3 parameter to Correctness module

5. **Create example domain proof (optional)**
   - Arith primitives as proof of concept

## Benefits

1. **No Prim postulates** - Everything is proven or parameterized
2. **Semantics definitional** - eval (Prim _ sem _) x = sem x
3. **Clean separation** - Contract vs Proof
4. **Domain compiler interface** - Clear API for Arith, String, etc.
5. **Slot-based** - Matches X86v3 architecture
