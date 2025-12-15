# Apply Proof Strategy: Closure Provenance Tracking

## Overview

This document describes the strategy for proving `apply` correctness in the Once language formal verification. The `apply` case is the most challenging proof because it involves a dynamic jump (via `blr`/`call`/`jalr`) to a code address stored in a closure.

## The Challenge

When proving compiler correctness, we need to show that executing the generated code produces the same result as the IR semantics. For most IR constructs, this is straightforward because the code flow is static.

However, `apply` presents a unique challenge:

```agda
-- apply: 6 instructions (AArch64)
compile-aarch64 apply =
  ldr x9 (base x0) ∷         -- load closure from pair.fst
  ldr x10 (base+imm x0 8) ∷  -- load arg from pair.snd
  ldr x19 (base x9) ∷        -- load env from closure
  ldr x9 (base+imm x9 8) ∷   -- load code-ptr from closure
  mov x0 (reg x10) ∷         -- arg → x0
  blr x9 ∷ []                -- JUMP TO DYNAMIC ADDRESS
```

The `blr x9` instruction jumps to whatever address is stored in x9, which came from the closure's code-ptr field. From the proof's perspective, this is a jump to an unknown location.

## Key Insight: Closure Provenance

The insight that makes this provable is that **closures are created by `curry`**, and the thunk code is embedded inline in the same program:

```
curry f codegen (at position N):
  N+0:  sub sp, sp, #16      -- allocate closure
  N+1:  str x0, [sp]         -- store env
  N+2:  mov x9, #6           -- code-ptr = 6 (RELATIVE!)
  N+3:  str x9, [sp+8]       -- store code-ptr
  N+4:  mov-from-sp x0       -- return closure pointer
  N+5:  b end                -- skip thunk
  N+6:  label 6              -- THUNK ENTRY POINT
  N+7:  sub sp, sp, #16      -- allocate pair
  N+8:  stp x19, x0, [sp]    -- store (env, arg)
  N+9:  mov-from-sp x0       -- x0 = pair pointer
  N+10 to N+9+|f|: f         -- execute f
  N+10+|f|: ret              -- return
  N+11+|f|: label end
```

The closure stores `code-ptr = 6`, which is the offset to the thunk entry point.

## Critical Limitation: Relative vs Absolute Addresses

**Current codegen uses RELATIVE offsets, but `blr` expects ABSOLUTE addresses.**

Looking at the codegen:
```agda
code-ptr = 6  -- hardcoded relative offset
...
mov x9 (imm code-ptr) ∷  -- stores literal 6 in x9
```

This means `blr x9` jumps to address 6, regardless of where `curry` appears in the program!

### Implications

1. **The code is only correct when curry is at position 0** (prefix = [])
2. For general programs with curry at position N, `blr x9` would need to jump to N+6, but it jumps to 6
3. This affects ALL backends (x86, RISC-V, AArch64)

### Correct Fix (Future Work)

The codegen should compute absolute addresses. One approach:
```agda
-- Instead of:
mov x9 (imm 6) ∷

-- Use position-independent code or compute:
adr x9, thunk_label ∷  -- ARM's address-of-label instruction
```

Or use a linker-style approach where labels are resolved to absolute addresses.

## Current POC Approach

For this proof-of-concept, we demonstrate the proof strategy with appropriate postulates that document the assumption:

### 1. Helper Lemmas Added to Foundation.agda

```agda
-- Step a blr instruction at arbitrary offset
step-blr-at-offset : ∀ (prefix : Program) (r : Reg) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ blr r ∷ suffix) s ≡
    just (record s { regs = writeReg (regs s) x30 (pc s +ℕ 1)
                   ; pc = readReg (regs s) r })

-- After blr, x30 holds the return address
blr-x30-is-return : ∀ (s : State) (r : Reg) →
  readReg (blr-result s r) x30 ≡ pc s +ℕ 1

-- Step a ret instruction (sets halted = true)
step-ret-at-offset : ∀ (prefix : Program) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ ret ∷ suffix) s ≡ just (record s { halted = true })
```

### 2. Cross-Register Preservation Lemmas

For the apply proof, we need to track that writing x30 (link register) doesn't affect other registers:

```agda
readReg-writeReg-x30-x0  : ∀ rf v → readReg (writeReg rf x30 v) x0  ≡ readReg rf x0
readReg-writeReg-x30-x9  : ∀ rf v → readReg (writeReg rf x30 v) x9  ≡ readReg rf x9
readReg-writeReg-x30-x19 : ∀ rf v → readReg (writeReg rf x30 v) x19 ≡ readReg rf x19
readReg-writeReg-x30-x20 : ∀ rf v → readReg (writeReg rf x30 v) x20 ≡ readReg rf x20
```

### 3. Proof Structure for Apply

The proof would proceed as:

```
1. Execute 5 setup instructions (ldr×4, mov)
   → x9 = code-ptr (currently 6)
   → x19 = env from closure
   → x0 = argument

2. ASSUMPTION: code-ptr (6) is valid in current program
   (This is where the codegen limitation matters)

3. Execute blr x9
   → pc = 6 (thunk entry)
   → x30 = return address

4. Execute thunk code:
   - sub sp, #16; stp x19, x0, [sp]; mov-from-sp x0
   - This constructs pair (env, arg) in x0
   - Then executes f via recursive run-ir-at-offset

5. Execute ret
   → halted = true

6. Result: x0 = encode (eval f (env, arg)) = closure(arg)
```

## Files Modified

| File | Changes |
|------|---------|
| `formal/Once/Backend/AArch64/Correct/Foundation.agda` | Added `step-blr-at-offset`, `blr-*` lemmas, `step-ret-at-offset`, cross-register lemmas |

## Success Criteria (POC)

- [x] `step-blr-at-offset` proven
- [x] `blr-*` helper lemmas proven
- [x] `step-ret-at-offset` proven
- [x] Cross-register preservation lemmas for x30, x10
- [x] `make aarch64` succeeds
- [x] Documentation complete

## Second Limitation: Execution Count Mismatch (RESOLVED)

**Status: This limitation has been resolved by understanding the correct semantics.**

The original concern was about the type signature:

```agda
run-ir-at-offset-apply : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
  halted s ≡ false → pc s ≡ length prefix → readReg (regs s) x0 ≡ encode x →
  ∃[ s' ] (exec (compile-length apply) ... s ≡ just s'  -- compile-length apply = 6
         × halted s' ≡ false × pc s' ≡ length prefix + 6
         × readReg (regs s') x0 ≡ encode (eval apply x)   -- THIS IS THE PROBLEM
         × ...)
```

**Key Insight:** The current type claims `x0 = encode (eval apply x)` after only 6 steps, but this is IMPOSSIBLE because:

1. apply's 6 instructions set up for the call (ldr×4, mov, blr)
2. After blr, pc jumps to thunk code (which is NOT part of apply's 6 instructions)
3. The thunk hasn't executed yet, so x0 doesn't contain the result

The actual execution path is:

```
Instructions in apply (6 total):
  0: ldr x9, [x0]
  1: ldr x10, [x0, #8]
  2: ldr x19, [x9]
  3: ldr x9, [x9, #8]
  4: mov x0, x10
  5: blr x9               -- JUMPS to thunk!

After blr, execution continues at thunk (NOT counted in apply):
  +0: sub sp, #16
  +1: stp x19, x0, [sp]
  +2: mov-from-sp x0
  +3 to +2+|f|: f
  +3+|f|: ret             -- HALTS here
```

So the actual number of steps is: 6 + 3 + compile-length f + 1 = 10 + compile-length f

But the type says `exec 6`, which would only execute the setup instructions and blr. After blr, we'd be at the thunk entry, NOT halted, but `exec 6` would return a state where `pc = code-ptr` and `halted = false`.

### Solution: Split into Setup + Thunk Execution

The correct approach is to split the proof into two parts:

**Part 1: `run-apply-setup`** - Prove apply's 6 instructions correctly set up:

```agda
-- What apply's 6 instructions actually do (provable!)
run-apply-setup : ∀ {A B} (prefix suffix : Program)
  (closure : ⟦ A ⇒ B ⟧) (arg : ⟦ A ⟧) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode (closure , arg) →
  ∃[ s' ] (exec 6 (prefix ++ compile-aarch64 apply ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ closure-code-ptr closure        -- PC at thunk entry
         × readReg (regs s') x19 ≡ closure-env closure  -- env loaded
         × readReg (regs s') x0 ≡ encode arg       -- arg in x0
         × readReg (regs s') x30 ≡ length prefix + 6)  -- return address
```

**Part 2: `run-thunk-at-offset`** - Prove thunk execution is correct:

```agda
-- Thunk executes correctly when called with proper setup
run-thunk-at-offset : ∀ {A B C} (f : IR (A * B) C)
  (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →                    -- at thunk entry
  readReg (regs s) x19 ≡ encode env →       -- env in x19
  readReg (regs s) x0 ≡ encode arg →        -- arg in x0
  ∃[ s' ] (exec (4 + compile-length f) (prefix ++ thunk-code f ++ suffix) s ≡ just s'
         × halted s' ≡ true                  -- ret halts
         × readReg (regs s') x0 ≡ encode (eval f (env , arg)))
```

**Part 3: Compose for full apply semantics**

For a complete program with `curry f` followed by `apply`, the proof chains:
1. curry creates closure with code-ptr pointing to thunk
2. apply's setup loads closure data and jumps to thunk
3. thunk executes f and returns

## Path Forward

### Short Term: Complete POC with Postulate

Add a `ClosureCodePtrValid` postulate that captures the assumption:

```agda
postulate
  ClosureCodePtrValid : ∀ {A B} (closure : ⟦ A ⇒ B ⟧) (prog : Program) →
    -- If closure was created by curry f at position 0 in prog,
    -- then the code-ptr stored in the closure points to valid thunk code
    ∃[ thunk-offset ] (closure-code-ptr closure ≡ thunk-offset
                      × ThunkAt thunk-offset prog)
```

### Medium Term: Fix Codegen

Update all backends to use absolute addresses:

1. **Option A**: Position-independent code (PC-relative addressing)
   - AArch64: Use `adr` instruction
   - x86: Use RIP-relative addressing
   - RISC-V: Use `auipc` + `addi`

2. **Option B**: Two-pass compilation
   - First pass: compute code layout
   - Second pass: emit code with resolved addresses

3. **Option C**: Runtime patching
   - Emit placeholder, patch at load time

### Long Term: Full Proof

Once codegen is fixed:
1. Remove the postulate
2. Prove curry stores correct absolute address
3. Prove apply's blr jumps to correct thunk
4. Complete end-to-end proof

## Conclusion

The apply proof is achievable but requires either:
1. A codegen fix to use absolute addresses, OR
2. A restricted proof for the case where curry is at position 0

The POC demonstrates the proof structure and helper lemmas needed. The main blocker is the relative-address limitation in the current codegen, which affects all three backends.
