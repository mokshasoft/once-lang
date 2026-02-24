# X86v3 Capacity Migration Plan

## Goal

Eliminate all 4 capacity-related postulates in X86v3 by migrating to X86's dynamic capacity threading pattern.

### Current Postulates

1. `pb-cap₁` in ComposeWF.agda (line 181)
2. `program-bound-cap₁` in PairWF.agda (line 175)
3. `program-bound-cap-pair` in ApplyWF.agda (line 275)
4. `slot-bounded-apply` in ApplyWF.agda (line 353)

## Root Cause Analysis

X86v3 tries to maintain **global invariants** through structural recursion:
- `CapacityInvariant`: `ps + 2*ps*pb ≤ cap`
- `program-bound-cap`: `slot + ps*pb ≤ cap`

This fails because:
1. Different closures have different body sizes
2. The slot grows during execution
3. The "slack" for nested calls diminishes as we recurse

## X86's Solution (Works)

X86 uses **dynamic capacity threading**:

```
┌─────────────────────────────────────────────────────┐
│ Initial: cap ≥ apply-consumed-slots + max-thunk-cap │
└─────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────┐
│ Curry: Creates closure with thunk-capacity = N      │
│        Outputs ClosureWFOutput with cwf-cap proof   │
└─────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────┐
│ Compose/Pair: Threads ClosureWFOutput through       │
│               NO global invariants needed!          │
└─────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────┐
│ Apply: Receives ApplyReady with ar-capacity         │
│        Uses closure's specific capacity             │
└─────────────────────────────────────────────────────┘
```

Key X86 types:

- **ClosureWellFormed** (ClosureWellFormed.agda:108-149): Each closure carries `thunk-capacity : ℕ`
- **ClosureWFOutput** (StarBase.agda:96-116): Carries capacity proof WITH the closure value
- **ApplyReady** (StarBase.agda:329-359): Provides `ar-capacity` matching what closure needs

## X86v3's Current Pattern (Has Postulates)

```
┌─────────────────────────────────────────────────────┐
│ Initial: CapacityInvariant + program-bound-cap      │
└─────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────┐
│ Compose/Pair: Tries to preserve program-bound-cap   │
│               FAILS: slot grows, slack shrinks      │
│               → POSTULATE pb-cap₁                   │
└─────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────┐
│ Apply: Needs program-bound-cap for ANY body         │
│        Can't derive from inputs                     │
│        → POSTULATE program-bound-cap-pair           │
└─────────────────────────────────────────────────────┘
```

## Migration Steps

### Step 1: Simplify `BodyCorrect.execute`

**File:** `ClosureWellFormed.agda` (lines 154-167)

**Current:**
```agda
execute : ∀ (arg : ⟦ A ⟧) (arg-loc pair-loc : ValueLocation FS)
  (s : LocState FS) (alloc : AllocState {FS}) →
  ValidAtWF alloc (pair env arg) pair-loc s →
  BeforeFrontier alloc pair-loc →
  halted s ≡ false →
  readReg (regs s) RDI ≡ pair-loc →
  next-slot alloc + body-capacity ≤ frame-capacity alloc →  -- KEEP
  CapacityInvariant alloc →                                  -- DELETE
  next-slot alloc + pair-slots *ℕ bound ≤ frame-capacity alloc → -- DELETE
  IRResultAWF body (pair env arg) s alloc
```

**New:**
```agda
execute : ∀ (arg : ⟦ A ⟧) (arg-loc pair-loc : ValueLocation FS)
  (s : LocState FS) (alloc : AllocState {FS}) →
  ValidAtWF alloc (pair env arg) pair-loc s →
  BeforeFrontier alloc pair-loc →
  halted s ≡ false →
  readReg (regs s) RDI ≡ pair-loc →
  next-slot alloc + body-capacity ≤ frame-capacity alloc →  -- ONLY constraint
  IRResultAWF body (pair env arg) s alloc
```

### Step 2: Simplify `RecDispatcherWF`

**File:** `ClosureWellFormed.agda` (lines 335-349)

**Current:**
```agda
RecDispatcherWF : ℕ → Set
RecDispatcherWF bound = ∀ {A B} (ir : IR A B) →
  ir-size ir < bound →
  (x : ⟦ A ⟧) (input-loc : ValueLocation FS) (s : LocState FS)
  (alloc : AllocState {FS}) →
  ValidAtWF alloc x input-loc s →
  BeforeFrontier alloc input-loc →
  halted s ≡ false →
  readReg (regs s) RDI ≡ input-loc →
  next-slot alloc + pair-slots *ℕ ir-size ir ≤ frame-capacity alloc →  -- KEEP
  CapacityInvariant alloc →                                             -- DELETE
  next-slot alloc + pair-slots *ℕ program-bound ≤ frame-capacity alloc → -- DELETE
  IRResultAWF ir x s alloc
```

**New:**
```agda
RecDispatcherWF : ℕ → Set
RecDispatcherWF bound = ∀ {A B} (ir : IR A B) →
  ir-size ir < bound →
  (x : ⟦ A ⟧) (input-loc : ValueLocation FS) (s : LocState FS)
  (alloc : AllocState {FS}) →
  ValidAtWF alloc x input-loc s →
  BeforeFrontier alloc input-loc →
  halted s ≡ false →
  readReg (regs s) RDI ≡ input-loc →
  next-slot alloc + pair-slots *ℕ ir-size ir ≤ frame-capacity alloc →  -- ONLY constraint
  IRResultAWF ir x s alloc
```

### Step 3: Update ComposeWF.agda

**File:** `IR/ComposeWF.agda`

Remove `inv` and `pb-cap` parameters from `run-compose` and recursive calls.

**Changes:**
1. Remove `CapacityInvariant alloc →` parameter (line 90)
2. Remove `next-slot alloc + pair-slots *ℕ program-bound ≤ frame-capacity alloc →` parameter (line 91)
3. Remove `inv₁` derivation and `pb-cap₁` postulate (lines 155-181)
4. Update recursive calls to `rec-wf` to not pass these arguments

### Step 4: Update PairWF.agda

**File:** `IR/PairWF.agda`

Same changes as ComposeWF:
1. Remove `CapacityInvariant alloc →` parameter (line 99)
2. Remove `next-slot alloc + pair-slots *ℕ program-bound ≤ frame-capacity alloc →` parameter (line 101)
3. Remove `inv₁` and `program-bound-cap₁` postulate (lines 163-175)
4. Update recursive calls

### Step 5: Update ApplyWF.agda

**File:** `IR/ApplyWF.agda`

**Current signature:**
```agda
run-apply : ... →
  next-slot alloc + pair-slots *ℕ ir-size (apply {A} {B}) ≤ frame-capacity alloc →
  CapacityInvariant alloc →
  next-slot alloc + pair-slots *ℕ program-bound ≤ frame-capacity alloc →
  IRResultAWF (apply {A} {B}) x s alloc
```

**New signature:**
```agda
run-apply : ... →
  next-slot alloc + pair-slots + body-capacity ≤ frame-capacity alloc →
  IRResultAWF (apply {A} {B}) x s alloc
```

Where `body-capacity` is extracted from the closure's `BodyCorrect.body-capacity`.

**Key change:** Apply derives `body-combined-cap` directly from:
- Input capacity constraint: `slot + ps + body-cap ≤ cap`
- No global invariant needed!

### Step 6: Update Entry Point

**File:** `WholeProgram.agda` (or wherever initial capacity is established)

Ensure initial capacity:
```agda
initial-cap : cap ≥ pair-slots * (1 + max-body-size)
-- or equivalently: cap ≥ pair-slots * program-bound * 2
```

This guarantees enough capacity for the deepest call chain.

### Step 7: Handle `slot-bounded-apply`

The `slot-bounded-apply` postulate (ApplyWF.agda:353) may require stack reclamation:

**Option A:** Use existing `reclaimable-slot` infrastructure
- After body executes, the result is at `reclaimable-slot`
- Show that `reclaimable-slot ≤ initial-slot + apply-overhead`

**Option B:** Accept that `ir-stack-requirement apply` doesn't capture dynamic body execution
- Change `ir-stack-requirement apply` to return a larger static bound
- Or document that apply's stack usage depends on the specific closure

## Expected Results

After migration:

| File | Postulate | Status |
|------|-----------|--------|
| ComposeWF.agda | `pb-cap₁` | ELIMINATED (no `pb-cap` to thread) |
| PairWF.agda | `program-bound-cap₁` | ELIMINATED (no `program-bound-cap₁` to thread) |
| ApplyWF.agda | `program-bound-cap-pair` | ELIMINATED (uses closure's `body-capacity`) |
| ApplyWF.agda | `slot-bounded-apply` | Requires reclamation or bound adjustment |

## Why This Works

The key insight is that X86v3 should **stop trying to maintain `program-bound-cap` through recursion**.

Instead:
1. Initial capacity is large enough for worst-case
2. Each closure knows its own body requirement (`body-capacity`)
3. Apply verifies it has enough for `pair-slots + body-capacity`
4. No global invariant threading needed

This matches how a real implementation works: the stack frame is sized at entry, and each function call checks it has enough space for its specific needs.

## References

- X86's ClosureWellFormed: `Once/Backend/X86/Correct/ClosureWellFormed.agda`
- X86's ClosureWFOutput: `Once/Backend/X86/Correct/StarBase.agda:96-116`
- X86's ApplyReady: `Once/Backend/X86/Correct/StarBase.agda:329-359`
- X86's Apply: `Once/Backend/X86/Correct/IR/Apply.agda`
