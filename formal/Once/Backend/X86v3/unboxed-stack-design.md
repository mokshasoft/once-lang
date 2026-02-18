# Unboxed Stack / Boxed Heap Design for SlotMachine

## Overview

Transform SlotMachine from a fully-boxed representation to a hybrid unboxed stack / boxed heap approach, enabling more efficient memory layout while maintaining correctness proofs.

## Current State (Boxed)

Currently, SlotMachine stores `ValueLocation` (pointers) everywhere:
- Memory: `Frame -> Slot -> Maybe ValueLocation`
- Fixed slot sizes: `pair-slots = 2`, `closure-slots = 2`
- All values accessed through pointer indirection

### Current Pair Representation

```
Pair (a, b) at slot S:
  slot[S]   = ValueLocation pointing to a
  slot[S+1] = ValueLocation pointing to b

Total: 2 slots (always), regardless of a and b's types
```

### Current Closure Representation

```
Closure at slot S:
  slot[S]   = ValueLocation pointing to env
  slot[S+1] = ValueLocation pointing to code

Total: 2 slots (always)
```

## Target State (Unboxed Stack / Boxed Heap)

### Proposed Pair Representation (Unboxed)

```
Pair (a, b) at slot S:
  slot[S .. S + type-slots A - 1] = unboxed value a
  slot[S + type-slots A .. S + type-slots A + type-slots B - 1] = unboxed value b

Total: type-slots A + type-slots B slots
```

### Type Slots Function

```agda
type-slots : Type -> Nat
type-slots Unit = 0
type-slots Void = 0
type-slots Int = 1
type-slots Float = 1       -- or 2 for 64-bit floats
type-slots Str = 1         -- pointer to string data
type-slots Buffer = 1      -- pointer to buffer data
type-slots (A * B) = type-slots A + type-slots B
type-slots (A + B) = 1 + max (type-slots A) (type-slots B)  -- tag + payload
type-slots (A => B) = 2    -- closure: env-ptr + code-ptr (always boxed)
type-slots (Fix F) = 1     -- pointer to recursive structure (always boxed)
type-slots (Eff A B) = type-slots B  -- result type determines slots
type-slots (TVar _) = 1    -- polymorphic = pointer
```

## Hybrid Approach

### Stack-Allocated (Unboxed)

Non-escaping, non-recursive values:
- Pairs of unboxed types
- Sum types (tag + unboxed payload)
- Base types (Int, Float)

### Heap-Allocated (Boxed)

Values requiring indirection:
- **Closures**: Always boxed because code pointer must be a location
- **Recursive types (`Fix F`)**: Self-referential structure requires indirection
- **Escaping values**: Values that may outlive current frame

## Sum Type Representation

For `A + B`:
- Slot 0: Tag (0 = left/inj₁, 1 = right/inj₂)
- Slots 1..max(type-slots A, type-slots B): Payload

```
inj₁ a at slot S:
  slot[S] = 0 (tag)
  slot[S+1 .. S + type-slots A] = unboxed value a
  (remaining slots unused)

inj₂ b at slot S:
  slot[S] = 1 (tag)
  slot[S+1 .. S + type-slots B] = unboxed value b
  (remaining slots unused)
```

Total slots: 1 + max(type-slots A, type-slots B)

## Recursive Type Representation

For `Fix F`:
- Always stored as a pointer to heap-allocated structure
- The unfolded value `F` is on the heap with its own layout

```
fold v at slot S:
  slot[S] = HeapRef pointing to unfolded value

On heap at HeapRef:
  [layout for type F]
```

## ValidAt Changes

### Current ValidAt for Pairs

```agda
valid-pair : ... ->
  readLoc s pair-loc ≡ just fst-loc ->
  readLoc s (sucLoc pair-loc) ≡ just snd-loc ->
  ...
  ValidAt alloc {A * B} (a , b) pair-loc s
```

### Proposed ValidAt for Unboxed Pairs

```agda
valid-pair-unboxed : forall {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
  {pair-loc : ValueLocation FS} {s : LocState FS} ->
  -- a is valid starting at pair-loc
  ValidAt alloc a pair-loc s ->
  -- b is valid starting at offset position
  ValidAt alloc b (offsetLoc pair-loc (type-slots A)) s ->
  ValidAt alloc {A * B} (a , b) pair-loc s
```

### ValidAt for Sum Types

```agda
valid-inl : forall {A B} {a : ⟦ A ⟧} {sum-loc : ValueLocation FS} {s} ->
  -- tag slot contains 0 (left)
  readSlotTag s sum-loc ≡ 0 ->
  -- payload contains ValidAt for a
  ValidAt alloc a (sucLoc sum-loc) s ->
  ValidAt alloc {A + B} (inj₁ a) sum-loc s

valid-inr : forall {A B} {b : ⟦ B ⟧} {sum-loc : ValueLocation FS} {s} ->
  -- tag slot contains 1 (right)
  readSlotTag s sum-loc ≡ 1 ->
  -- payload contains ValidAt for b
  ValidAt alloc b (sucLoc sum-loc) s ->
  ValidAt alloc {A + B} (inj₂ b) sum-loc s
```

### ValidAt for Recursive Types

```agda
valid-fold : forall {F} {v : ⟦ F ⟧} {loc : ValueLocation FS} {s} ->
  -- slot contains pointer to heap-allocated unfolded value
  readLoc s loc ≡ just heap-loc ->
  BeforeFrontier alloc heap-loc ->
  ValidAt alloc v heap-loc s ->
  ValidAt alloc {Fix F} (fold v) loc s
```

## Stack vs Heap Decision

Escape analysis determines allocation mode:
- **Non-escaping** -> StackAlloc (unboxed on stack)
- **Escaping** -> HeapAlloc (boxed, pointer stored on stack)

The IR itself specifies allocation mode after an escape analysis pass.

### Closure Design Rationale

Closures remain boxed (2 slots: env-ptr + code-ptr) because:
1. Code pointer must be a location (can't inline code in stack)
2. Environment may escape (passed to other functions)
3. Closure may be returned (must outlive creating frame)

### Recursive Type Design Rationale

Recursive types (`Fix F`) remain boxed because:
1. Self-referential structure requires indirection
2. Size not known at compile time for arbitrary unfolding
3. Must handle cyclic references

## Memory Type Changes

### Current Memory Type

```agda
StackMem FS = Frame -> Slot -> Maybe (ValueLocation FS)
```

### Option A: Keep ValueLocation, Interpret Differently

Stack slots contain either:
- Raw value (for unboxed base types)
- Pointer (for boxed/closure/recursive)

Interpretation determined by type context at use site.

### Option B: Typed Memory

```agda
data SlotValue where
  raw-word : Word -> SlotValue         -- unboxed data
  location : ValueLocation FS -> SlotValue  -- pointer

StackMem FS = Frame -> Slot -> Maybe SlotValue
```

## Allocation Changes

### Current Allocation

```agda
ir-stack-requirement ⟨ f , g ⟩ = ir-req f + ir-req g + pair-slots
```

### Proposed Allocation

```agda
ir-result-type : forall {A B} -> IR A B -> Type
ir-result-type {_} {B} _ = B

ir-stack-requirement : forall {A B} -> IR A B -> Nat
ir-stack-requirement {_} {B} ⟨ f , g ⟩ =
  ir-req f + ir-req g + type-slots B
```

## IR Handler Changes

### PairWF Changes

```agda
-- Current: allocates pair-slots = 2
pair-loc = OnStack frame (next-slot alloc)
alloc' = record alloc { next-slot = next-slot alloc + pair-slots }

-- Proposed: allocates type-slots (B * C)
result-slots = type-slots B + type-slots C
pair-loc = OnStack frame (next-slot alloc)
alloc' = record alloc { next-slot = next-slot alloc + result-slots }
```

### CurryWF (Unchanged)

Closures always use 2 slots (env-ptr + code-ptr) because:
- Code pointer is always a reference
- Environment may escape

### New Handlers

- `InlWF.agda` - allocate `1 + type-slots A` (tag + payload)
- `InrWF.agda` - allocate `1 + type-slots B` (tag + payload)
- `CaseWF.agda` - no allocation, dispatch to branches based on tag
- `FoldWF.agda` - heap allocate, return pointer
- `UnfoldWF.agda` - dereference pointer
- `InitialWF.agda` - absurd elimination (no code generated)
- `ArrWF.agda` - effect lifting

## Key Design Decisions

1. **Closures always boxed**: env-ptr + code-ptr representation
2. **Recursive types always boxed**: `Fix F` stores pointer
3. **Sum types**: tag + max(payload) slots, unboxed if non-escaping
4. **Base types**: Int/Float unboxed, Str/Buffer are pointers to heap data
5. **Escape analysis boundary**: IR specifies StackAlloc vs HeapAlloc

## Migration Path

1. Add `type-slots` function to `Once/Type.agda`
2. Migrate X86v3/Types.agda to import from `Once.Type`
3. Migrate X86v3/IR.agda to import from `Once.IR`
4. Extend Validity for sum/recursive types
5. Add new IR handlers
6. Update existing handlers to use type-slots
7. Update Dispatcher for all IR cases
8. Update SlotMachine for unboxed values

## Verification

After each step:
```bash
make agda MODULE=Once/Type.agda
make agda MODULE=Once/Backend/X86v3/Types.agda
make agda MODULE=Once/Backend/X86v3/IR.agda
make agda MODULE=Once/Backend/X86v3/Validity.agda
make agda MODULE=Once/Backend/X86v3/Dispatcher.agda

# Check no new postulates
grep -rn "postulate" formal/Once/Backend/X86v3/
```
