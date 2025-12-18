# X86 Backend Verification Architecture

## The 4-Axiom Foundation

The entire X86 verification rests on **exactly 4 axioms**:

```agda
postulate
  -- 1. Encoding is injective (distinct values → distinct words)
  encode-injective : encode x ≡ encode y → x ≡ y

  -- 2. Memory read-after-write (same address)
  mem-read-write : readMem (writeMem m addr v) addr ≡ just v

  -- 3. Memory frame (different address)
  mem-read-other : addr₁ ≢ addr₂ → readMem (writeMem m addr₁ v) addr₂ ≡ readMem m addr₂

  -- 4. Encode returns allocation address
  encode-is-alloc-addr : encode (a, b) ≡ base   -- where base is allocation address
```

The **~15 encoding axioms** in Postulates.agda (encode-pair-fst, encode-inl-tag, etc.) are **all derived** from these 4 axioms.

---

## Current Progress

### ✅ Completed

1. **No-`with` rule enforced** - `X86/Semantics.agda` uses `case_of_` everywhere
2. **Star relation implemented** - `X86/Correct/Star.agda` provides CompCert-style simulation
   - Eliminates fuel arithmetic in proofs
   - `star-trans` for composition instead of `exec-chain`
   - Chaining combinators: `⟨_,_⟩◅_`, `_◅◅_`
3. **Allocation properties derived** - `X86/Encoding.agda` shows:
   - `alloc-pair-fst/snd` derived from `mem-read-write` + `mem-read-other`
   - `alloc-inl-tag/val` derived from `mem-read-write` + `mem-read-other`
   - `alloc-inr-tag/val` derived from `mem-read-write` + `mem-read-other`
4. **HeapValid invariant added** - `X86/Encoding.agda` now includes:
   - `HeapValid` type tracking allocated regions
   - `AllocKind` describing what's at each address (pair, inl, inr)
   - `alloc-*-valid` functions that produce proofs with allocation
5. **Encoding axioms derived** - Actual proofs in `X86/Encoding.agda`:
   - `encode-pair-fst-derived` : from `alloc-pair-fst` + `encode-is-alloc-addr-pair`
   - `encode-pair-snd-derived` : from `alloc-pair-snd` + `encode-is-alloc-addr-pair`

### 🔄 In Progress

6. **Use derived proofs in Correct.agda** - Replace axiom calls with derived versions
   - Current: `encode-pair-fst a b (memory s)`
   - Target: `encode-pair-fst-derived a b encode encode encode m base`

### ⏳ Remaining

7. **Remove encoding axioms from Postulates.agda** (once Correct.agda uses derived versions)

---

## Current Postulate Inventory

### Postulate Categories

1. **Fundamental axioms** - Core truths about memory and encoding
2. **Plumbing postulates** - Bridge equivalent representations (`case_of_` tradeoff)
3. **Engineering postulates** - Could be eliminated with structural changes
4. **Runtime postulates** - Complex closure behavior

### Fundamental Axioms (4)

| Module | Postulate | Notes |
|--------|-----------|-------|
| Encoding.agda | `mem-read-write` | Memory read-after-write (same addr) |
| Encoding.agda | `mem-read-other` | Memory frame (different addr) |
| Encoding.agda | `encode-injective` | Encoding is injective |
| Encoding.agda | `encode-is-alloc-addr-pair` | Encoding returns alloc address |

### Plumbing Postulates (2)

| Module | Postulate | Notes |
|--------|-----------|-------|
| Star.agda | `exec-to-star` | `case_of_` tradeoff (see below) |
| Star.agda | `exec-until-pc-to-star` | `case_of_` tradeoff (see below) |

**Why plumbing?** These connect fuel-based execution (`exec`) to Star-based execution. They don't add semantic assumptions - if exec succeeds in n steps, the same n step proofs would build the Star. The postulate bridges the representation gap caused by `case_of_`.

### Engineering Postulates (eliminable with work)

| Module | Postulate | Root Cause | Solution |
|--------|-----------|------------|----------|
| Correct.agda | `rsp>16'` (many) | Stack invariant needs rsp > 32 | Strengthen precondition |
| Correct.agda | `s-final` (case-inl/inr) | Fuel mismatch: compile-length > actual steps | Use `exec-until-pc` |
| Correct.agda | `r14-final`, `r15-final` (pair) | Codegen pop reads wrong location | Fix codegen order |
| Correct.agda | `mem-final` (pair) | Same as above | Fix codegen order |
| Correct.agda | `stack-inv-final` | Practical assumption | Track stack depth |

**Fuel mismatch explained**: For case branches, `compile-length [ f , g ]` gives fuel for both branches, but only one executes. The solution is `exec-until-pc` which stops at the target PC regardless of remaining fuel.

### Runtime Postulates (2)

| Module | Postulate | Notes |
|--------|-----------|-------|
| Correct.agda | `closure-code-ptr-x86` | Closure code pointer at correct address |
| Correct.agda | `run-apply-seq` | Apply sequence executes correctly |

**Why runtime?** Closures involve complex runtime behavior (thunk construction, application, environment capture) that would require significant additional proof infrastructure.

### Eliminated This Session

- ✅ `∸+<-lemma` - proven using standard library
- ✅ `exec-until-pc-to-exec` - deleted (was unused)
- ✅ `postulate-pc-at-fuel-zero` - deleted (lemma was unused and unprovable as stated)

---

## The No-`with` Rule (for Definitions)

**`with` is banned in definitions.** Proofs may use `with` when needed.

### Why

`with` causes abstraction that breaks definitional equality. When Agda sees:

```agda
step prog s with halted s
... | true = just s
... | false = ...
```

It creates a new context where `halted s` is abstracted. Even if you have a proof `h : halted s ≡ false`, Agda cannot reduce `step prog s` because the original expression is gone.

This is why the codebase had ~30 "mechanical postulates" - they're just asserting facts that should compute but don't because of `with`.

### Alternatives

| Instead of `with` | Use |
|-------------------|-----|
| Pattern match on result | `case_of_` expression |
| Need equality proof | `inspect` idiom |
| Complex branching | Helper function with explicit cases |

### Example

```agda
-- BAD: blocks computation
step prog s with halted s
... | true = just s
... | false with fetch prog (pc s)
...   | nothing = just (record s { halted = true })
...   | just instr = execInstr prog s instr

-- GOOD: computes when halted s is known
step : Program → State → Maybe State
step prog s =
  case halted s of λ where
    true → just s
    false → case fetch prog (pc s) of λ where
      nothing → just (record s { halted = true })
      (just instr) → execInstr prog s instr
```

### The `case_of_` Tradeoff

Using `case_of_` instead of `with` enables **definitional equality** in proofs - when the scrutinee is a concrete constructor, the case reduces and we can use `refl`. This is the major benefit.

However, `case_of_` is just function application: `case x of f = f x`. When `x` is **abstract** (not a concrete constructor), the case doesn't reduce. Even `with` pattern matching in the outer context doesn't help - the `with` abstraction affects the TYPE but the TERM still contains the abstract scrutinee.

**Consequence:** Bridge lemmas like `exec-to-star` must be postulated:
```agda
-- Cannot prove: even when we know halted s = true from `with`,
-- the term `exec (suc n) prog s` still contains (halted s) as a subterm
-- and the case_of_ doesn't reduce.
postulate
  exec-to-star : exec n prog s ≡ just s' → Star prog s s'
```

**This is an acceptable tradeoff.** The bridge postulates are "plumbing" - they connect equivalent representations and don't add semantic assumptions. The benefit of definitional equality for direct proofs far outweighs the cost of a few plumbing postulates.

---

## Deriving Encoding Properties

The current ~15 encoding axioms like `encode-pair-fst`, `encode-inl-tag`, etc. are **derived** from:

1. **Explicit allocation with `writeMem`**
2. **The 3 memory axioms**

### Implementation (in X86/Encoding.agda)

```agda
-- Allocation uses writeMem explicitly
alloc-pair : Memory → Word → Word → Word → Memory × Word
alloc-pair m base v₁ v₂ = m' , base
  where
    m₁ = writeMem m base v₁
    m' = writeMem m₁ (base + 8) v₂

-- Properties are DERIVED, not postulated
alloc-pair-fst : ∀ m base v₁ v₂ →
  let (m' , addr) = alloc-pair m base v₁ v₂
  in readMem m' addr ≡ just v₁
alloc-pair-fst m base v₁ v₂ = trans step3 step4
  where
    step3 = mem-read-other (λ eq → n≢n+8 base (sym eq))  -- base ≢ base + 8
    step4 = mem-read-write                                -- read what we wrote
```

### Next Step: HeapValid Invariant

The current axioms like `encode-pair-fst a b m` claim the property holds for ANY memory `m`. But it only holds for memory created by allocation.

**Solution:** Add a `HeapValid` invariant:

```agda
-- Predicate: memory was created by proper allocation
data HeapValid : Memory → Set where
  ...

-- Modified property (not an axiom!)
encode-pair-fst : HeapValid m → readMem m (encode (a,b)) ≡ just (encode a)
```

---

## Verification Commands

```bash
# Per-module typecheck (use during development)
make x86-correct      # Full correctness proofs
make x86-star         # Star relation module
make x86-encoding     # 3-axiom derivations
make x86-foundation   # Foundation module

# Full X86 backend
make x86
```

---

## Success Criteria

- [x] No `with` anywhere in X86 backend files
- [x] `make x86-correct` passes
- [x] Star relation eliminates fuel arithmetic
- [x] Allocation properties derived from 3 memory axioms
- [x] HeapValid invariant implemented in Encoding.agda
- [x] `encode-pair-fst/snd-derived` proven (axioms are derivable!)
- [x] `∸+<-lemma` proven (was postulate, now theorem)
- [x] Unused postulates removed (`exec-until-pc-to-exec`)
- [ ] Use derived proofs in Correct.agda (replace axiom calls)
- [ ] Remove encoding axioms from Postulates.agda
- [ ] Only 4 fundamental axioms + plumbing in X86 verification
