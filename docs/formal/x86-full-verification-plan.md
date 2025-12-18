# Plan: CompCert-Style Simulation Proofs for X86 Backend

## Goal
Refactor the x86 backend proofs to use a simulation-based approach (Option 3), eliminating fuel management and step-counting complexity. This provides a cleaner, more maintainable architecture that scales to future changes.

## Prerequisites

**IMPORTANT: Read lessons learned first!**
Before implementing, read `docs/formal/lessons-learned.md` which contains critical insights:
- `with` patterns block computation (lines 58-77)
- `with` abstraction blocks definitional equality in step/exec proofs (lines 456-497)
- Layered postulate strategy (lines 346-369)
- The `run-ir-at-offset` pattern (lines 592-654)
- **Arithmetic lessons** (lines 130-238):
  - `refl` only works when all first arguments to `+` are concrete numbers (lines 130-193)
  - Use `m≤m+n` for large number comparisons, not structural induction (lines 194-238)
  - Example: `stackBase>16 = m≤m+n 17 2147418095` is O(1), structural would be billions of steps

Key quote: *"postulates at the `with`-boundary are unavoidable without rewriting the operational semantics, but everything above that layer can be proven by composition"*

---

## Architecture Overview

### Current Approach (Problems)
- Uses `exec n` (fuel-bounded) and `exec-until-pc` (target-bounded)
- Requires complex conversion between `exec` ↔ `exec-until-pc`
- Step-count arithmetic for chaining (e.g., `exec (7 + len-f + 2 + len-g + 6)`)
- `with` clauses in semantics block equational reasoning

### New Approach (CompCert-style)
- Use `_⟶*_` (star relation): reflexive-transitive closure of `step`
- Chaining is just transitivity (trivial)
- No fuel or step counts needed
- Simulation relation connects IR semantics to x86 execution

---

## Phase 1: Star Relation Infrastructure

### 1.1 Create `Correct/Star.agda`

Define the reflexive-transitive closure of `step`:

```agda
module Once.Backend.X86.Correct.Star where

-- Star transition relation
data _⟶*_ (prog : Program) : State → State → Set where
  -- Base: halted state (execution complete)
  done : ∀ {s} →
         halted s ≡ true →
         prog ⟶* s s

  -- Step: take one step, then continue
  more : ∀ {s s' s''} →
         halted s ≡ false →
         step prog s ≡ just s' →
         prog ⟶* s' s'' →
         prog ⟶* s s''
```

### 1.2 Prove Star Properties

```agda
-- Transitivity (key for composition!)
⟶*-trans : ∀ {prog s₁ s₂ s₃} →
           prog ⟶* s₁ s₂ →
           halted s₂ ≡ false →
           prog ⟶* s₂ s₃ →
           prog ⟶* s₁ s₃

-- Single step lifts to star
⟶*-step : ∀ {prog s s'} →
          halted s ≡ false →
          step prog s ≡ just s' →
          prog ⟶* s' s'' →
          prog ⟶* s s''

-- Reflexivity for non-halted (identity execution)
⟶*-refl : ∀ {prog s} → halted s ≡ false → prog ⟶* s s
-- NOTE: This only holds if we allow 0-step execution
-- May need to adjust definition
```

### 1.3 Bridge to `exec-until-pc`

```agda
-- Connect star to exec-until-pc (for reusing existing proofs)
exec-until-pc-to-star : ∀ {target fuel prog s s'} →
  exec-until-pc target fuel prog s ≡ just s' →
  halted s' ≡ true →
  prog ⟶* s s'

-- Connect star to exec (for simple cases)
exec-to-star : ∀ {n prog s s'} →
  exec n prog s ≡ just s' →
  halted s' ≡ true →
  prog ⟶* s s'
```

**Test**: `make agda MODULE=Once/Backend/X86/Correct/Star.agda`

---

## Phase 2: Simulation Relation

### 2.1 Create `Correct/Simulation.agda`

Define what it means for x86 state to simulate IR evaluation:

```agda
module Once.Backend.X86.Correct.Simulation where

-- Simulation relation: x86 state correctly represents IR computation
record Simulates {A B : Type} (ir : IR A B) (x : ⟦ A ⟧)
                 (prog : Program) (s : State) : Set where
  field
    -- Input is correctly encoded
    input-encoded : readReg (regs s) rdi ≡ encode x
    -- Execution hasn't halted yet
    not-halted : halted s ≡ false
    -- Stack invariant holds
    stack-inv : StackInvariant s
    -- Sufficient stack space
    rsp-valid : readReg (regs s) rsp > 16

-- Result relation: x86 state has correct output
record HasResult {A B : Type} (ir : IR A B) (x : ⟦ A ⟧)
                 (s : State) : Set where
  field
    -- Output is correctly encoded
    output-encoded : readReg (regs s) rax ≡ encode (eval ir x)
    -- Execution has halted
    is-halted : halted s ≡ true
```

### 2.2 Forward Simulation Theorem

The main theorem to prove for each IR constructor:

```agda
-- Forward simulation: if we start in a simulating state,
-- execution reaches a result state
forward-sim : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
              Simulates ir x (compile-x86 ir) s →
              pc s ≡ 0 →
              ∃[ s' ] ((compile-x86 ir) ⟶* s s' ×
                       HasResult ir x s')
```

**Test**: `make agda MODULE=Once/Backend/X86/Correct/Simulation.agda`

---

## Phase 3: Simple IR Cases

Prove forward simulation for non-recursive IR constructors:

### 3.1 Simple Cases (1-2 instructions each)
- `id` : `mov rax, rdi`
- `terminal` : `xor rax, rax`
- `initial` : absurd (no input of type Void)
- `fst` : `mov rax, [rdi]`
- `snd` : `mov rax, [rdi+8]`

### 3.2 Sum Constructors (4 instructions each)
- `inl` : allocate, set tag=0, store value, return ptr
- `inr` : allocate, set tag=1, store value, return ptr

### 3.3 Fold/Unfold (1 instruction each)
- `fold` : `mov rax, rdi` (identity on encoding)
- `unfold` : `mov rax, rdi`

**Strategy**: Each proof follows pattern:
1. Show `step` succeeds (may need postulate due to `with`)
2. Construct star proof using `more` constructor
3. Show final state has correct rax value

**Test**: `make agda MODULE=Once/Backend/X86/Correct/MutualIR.agda`

---

## Phase 4: Recursive IR Cases

### 4.1 Composition (`g ∘ f`)

```agda
sim-compose : ∀ {A B C} (f : IR A B) (g : IR B C) (x : ⟦ A ⟧) (s : State) →
              Simulates (g ∘ f) x prog s →
              ∃[ s' ] (prog ⟶* s s' × HasResult (g ∘ f) x s')
```

**Strategy**:
1. IH gives: `prog ⟶* s s-after-f` with `rax = encode (eval f x)`
2. Transfer: `prog ⟶* s-after-f s-transfer` (mov rdi, rax)
3. IH gives: `prog ⟶* s-transfer s-final` with `rax = encode (eval g (eval f x))`
4. Compose: `⟶*-trans` three times

### 4.2 Pair (`⟨ f , g ⟩`)

```agda
sim-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (x : ⟦ A ⟧) (s : State) →
           Simulates ⟨ f , g ⟩ x prog s →
           ∃[ s' ] (prog ⟶* s s' × HasResult ⟨ f , g ⟩ x s')
```

**Strategy**:
1. Setup: `prog ⟶* s s-setup` (push, allocate, save input)
2. IH f: `prog ⟶* s-setup s-after-f`
3. Middle: `prog ⟶* s-after-f s-middle` (store f result, restore input)
4. IH g: `prog ⟶* s-middle s-after-g`
5. Final: `prog ⟶* s-after-g s-final` (store g result, return pair ptr)
6. Compose: `⟶*-trans` five times

### 4.3 Case (`[ f , g ]`)

```agda
sim-case-inl : ∀ {A B C} (f : IR A C) (g : IR B C) (a : ⟦ A ⟧) (s : State) →
               Simulates [ f , g ] (inj₁ a) prog s →
               ∃[ s' ] (prog ⟶* s s' × HasResult [ f , g ] (inj₁ a) s')

sim-case-inr : ∀ {A B C} (f : IR A C) (g : IR B C) (b : ⟦ B ⟧) (s : State) →
               Simulates [ f , g ] (inj₂ b) prog s →
               ∃[ s' ] (prog ⟶* s s' × HasResult [ f , g ] (inj₂ b) s')
```

**Strategy**:
- No step-count mismatch! Star doesn't care which branch executes
- Just prove the taken branch reaches correct result

**Test**: `make agda MODULE=Once/Backend/X86/Correct/MutualIR.agda`

---

## Phase 5: Curry and Apply

### 5.1 Curry

```agda
sim-curry : ∀ {A B C} (f : IR (A * B) C) (a : ⟦ A ⟧) (s : State) →
            Simulates (curry f) a prog s →
            ∃[ s' ] (prog ⟶* s s' × HasResult (curry f) a s')
```

**Strategy**:
- Curry just builds closure, doesn't execute f
- 7 instructions to closure creation + jmp over thunk
- Thunk code is skipped (jumped over)

### 5.2 Apply

```agda
sim-apply : ∀ {A B} (closure : ⟦ A ⇒ B ⟧) (arg : ⟦ A ⟧) (s : State) →
            Simulates apply (closure , arg) prog s →
            ∃[ s' ] (prog ⟶* s s' × HasResult apply (closure , arg) s')
```

**Note**: Apply involves thunk execution. Keep `run-apply-seq` as axiom or use E2E-Trace validation approach.

**Test**: `make agda MODULE=Once/Backend/X86/Correct/MutualIR.agda`

---

## Phase 6: Main Theorem

### 6.1 Derive `codegen-x86-correct`

```agda
-- Main correctness theorem
codegen-x86-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  ∃[ s' ] ((compile-x86 ir) ⟶* (initWithInput x) s' ×
           HasResult ir x s')

codegen-x86-correct ir x = forward-sim ir x (initWithInput x)
                             (init-simulates ir x) refl
```

### 6.2 Derive `run` theorem (if needed for compatibility)

```agda
-- Convert star to run for backward compatibility
star-to-run : ∀ {prog s s'} →
  prog ⟶* s s' →
  halted s' ≡ true →
  run prog s ≡ just s'
```

**Test**: `make x86-correct`

---

## What Stays as Axioms

### Encoding Axioms (in `Postulates.agda`)
- `encode` : `⟦ A ⟧ → Word`
- `encode-unit`, `encode-pair-fst/snd`, `encode-inl/inr-*`
- `encode-pair-construct`, `encode-inl-construct`, `encode-inr-construct`
- These define the memory representation contract

### Closure Axioms
- `closure-code-ptr-x86`, `closure-env-x86`
- `encode-curry-construct`
- `run-apply-seq` (thunk execution)

### Step-Level Postulates
Due to `with` clauses in `step`/`execInstr`, we postulate:
- `step-mov`, `step-add`, `step-sub`, etc. (instruction execution facts)
- These form the "trusted execution semantics" layer
- Everything above is proven by composition

---

## Files to Create/Modify

| File | Action | Description |
|------|--------|-------------|
| `Correct/Star.agda` | **Create** | Star relation and properties |
| `Correct/Simulation.agda` | **Create** | Simulation and result relations |
| `Correct/MutualIR.agda` | **Modify** | Replace `run-ir-at-offset` with simulation proofs |
| `Correct/ExecLemmas.agda` | **Modify** | Add star ↔ exec bridges |

---

## Implementation Order

```
Phase 1 (Star)
    ↓
Phase 2 (Simulation relation)
    ↓
Phase 3 (Simple IR: id, fst, snd, inl, inr, terminal, fold)
    ↓
Phase 4 (Recursive IR: compose, pair, case)
    ↓
Phase 5 (Curry, Apply)
    ↓
Phase 6 (Main theorem)
```

Each phase: implement → test with `make agda MODULE=...` → commit → push

---

## Benefits of This Approach

1. **No fuel management**: Star relation has no fuel parameter
2. **No step-count arithmetic**: No `exec (7 + len-f + 2 + len-g + 6)`
3. **Trivial chaining**: Composition is just `⟶*-trans`
4. **Branch-agnostic**: Case doesn't need different step counts per branch
5. **Future-proof**: Adding new IR constructors fits naturally
6. **CompCert-proven**: This architecture has scaled to a full C compiler

---

## Future Opportunity: Code Generator Simplification

Once the simulation-based proofs are working, we can revisit the code generators themselves. Some complexity was added specifically to make step-counting proofs work:

### Potential Simplifications

1. **Remove alignment NOPs**
   - Current: Some code sequences have NOPs to align step counts
   - With star relation: No step counts, so alignment NOPs could be removed
   - Impact: Smaller generated code, simpler proofs

2. **Simplify jump targets**
   - Current: `compile-length` computes exact instruction counts for jump labels
   - With star relation: Could use relative jumps or simpler label scheme
   - **Note**: Computed labels may still be needed for correctness, but proofs become simpler

3. **Reconsider transfer instructions**
   - Current: `mov rdi, rax` between compose stages for step-counting
   - With star relation: Still needed semantically, but proof is simpler
   - Could potentially optimize calling convention (like RISC-V using same reg for in/out)

4. **Closure/thunk layout**
   - Current: `jmp 400` placeholder jumps over thunk code
   - With star relation: Same semantics, but proof that execution skips thunk is trivial

### When to Explore This

**After Phase 6 is complete and all proofs work with star relation**, consider:
1. Audit code generators for step-count-motivated complexity
2. Try removing unnecessary instructions
3. Re-verify with simulation proofs (should be straightforward)

This is a second-order benefit: simpler proofs → simpler code → even simpler proofs

---

## Verification

```bash
# After each phase
make agda MODULE=Once/Backend/X86/Correct/<file>.agda

# Full verification
make x86-correct

# Run E2E trace validation
make trace-test
```
