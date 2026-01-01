# Stateful Runner Implementation Example

This document shows a concrete example of implementing a stateful runner for the `id` IR generator, demonstrating the pattern that should be followed for all other cases.

## Current Implementation (encode-based)

From `StarBase.agda:151-184`:

```agda
run-id-star : ∀ {i A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →  -- ← Uses encode
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (id {i} {A}) ++ suffix
  in ∃[ s' ] IRStarResult (id {i} {A}) prog s s' x (length prefix)

run-id-star {i} {A} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (id {i} {A}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'  -- ← Proves: rax ≡ encode (eval id x) ≡ encode x
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-at-0 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv ...
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }
```

## Stateful Implementation (address-based)

To add to `StarBase.agda` (after line 1300):

```agda
------------------------------------------------------------------------
-- Stateful IR Runners (Phase 1: Simple Base Cases)
------------------------------------------------------------------------

-- | Stateful version of run-id-star
-- Identity: just moves input address from rdi to rax
run-id-star-s : ∀ {i A} (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →  -- ← Explicit address, NO encode!
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (id {i} {A}) ++ suffix
  in ∃[ s' ] IRStarResultS (id {i} {A}) prog s s' addr-in (length prefix)
  --  ↑ Returns address directly

run-id-star-s {i} {A} prefix suffix addr-in s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let -- Run the same low-level execution
      (s' , step-eq , h' , pc' , rax-eq') = run-id-at-offset {A} prefix suffix addr-in s h-false pc-eq rdi-eq
      --                                                        ↑ addr-in, not x!
      prog = prefix ++ compile-x86 (id {i} {A}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      
  -- Return IRStarResultS (with -s suffix on ir-rax field)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax-s = trans rax-eq' (cong (readReg (regs s)) rdi-eq)
      -- ↑ Proves: rax ≡ addr-in (direct address, no encoding!)
      --   rax-eq' gives: rax ≡ rdi
      --   rdi-eq gives:  rdi ≡ addr-in
      --   So: rax ≡ addr-in by transitivity
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-at-0 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }
```

## Key Differences

| Aspect | encode-based | Stateful |
|--------|-------------|----------|
| Input type | `x : ⟦ A ⟧` | `addr-in : Word` |
| Input precond | `rdi ≡ encode x` | `rdi ≡ addr-in` |
| Return type | `IRStarResult` | `IRStarResultS` |
| Result field | `ir-rax : rax ≡ encode (eval id x)` | `ir-rax-s : rax ≡ addr-in` |
| Proof strategy | Semantic equality through encode | Direct register equality |

## Why This Works

**For `id`**:
- `eval id x = x` (identity semantics)
- `encode x` is some address in memory
- But statefully: we don't care what `x` is!
- We just track: `addr-in` goes to `rax`
- No encoding postulates needed!

## Pattern for Other Simple Cases

### `terminal` (returns unit = 0)
```agda
run-terminal-star-s : ... →
  ∃[ s' ] IRStarResultS terminal prog s s' 0 offset
  --                                      ↑ Always 0 (unit encoding)
```

### `fold`/`unfold` (Fix is identity)
```agda
run-fold-star-s : ... (addr-in : Word) ... →
  ∃[ s' ] IRStarResultS fold prog s s' addr-in offset
  --                                    ↑ Same address (Fix ≅ A)
```

### `fst`/`snd` (already exist!)
These are in StarBase.agda:1300-1450 as `run-fst-star-s` and `run-snd-star-s`.
They use `PairAtS` validity predicates to extract components.

## Testing the Implementation

After adding `run-id-star-s`, test it:

```agda
-- Simple test: id with explicit address
test-id-stateful : ∀ {A : Type} (addr : Word) →
  let s0 = initWithInput {A} addr
      prog = compile-x86 (id {_} {A})
  in ∃[ s' ] (Star prog s0 s'
            × readReg (regs s') rax ≡ addr)  -- ← No encode!
test-id-stateful {A} addr =
  let (s' , res) = run-id-star-s {_} {A} [] [] addr s0 refl refl refl
                                 (stack-inv-init addr) (rsp>16-init addr) (rbp-inv-init addr)
  in s' , IRStarResultS.ir-star res , IRStarResultS.ir-rax-s res
```

## Next Steps

After implementing simple base cases:
1. Add `run-terminal-star-s`
2. Add `run-fold-star-s`, `run-unfold-star-s`
3. Add `run-arr-star-s`
4. Use existing `run-fst-star-s`, `run-snd-star-s`
5. Use existing `run-inl-star-s`, `run-inr-star-s` (from plan)

Then proceed to Phase 3 (compose), Phase 4 (pair), etc.

## Implementation Checklist

- [ ] Add `run-id-star-s` to StarBase.agda
- [ ] Add test `test-id-stateful`
- [ ] Verify builds: `make x86`
- [ ] Add `run-terminal-star-s`
- [ ] Add `run-fold-star-s`
- [ ] Add `run-unfold-star-s`
- [ ] Add `run-arr-star-s`
- [ ] Document pattern for compose (Phase 3)
- [ ] Implement stateful compose
- [ ] Continue with pair, case, curry/apply

Each checkmark represents working, tested code that brings us closer to zero encoding postulates!
