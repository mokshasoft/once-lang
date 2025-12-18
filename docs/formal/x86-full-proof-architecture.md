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

| Module | Postulate | Category | Notes |
|--------|-----------|----------|-------|
| Encoding.agda | `mem-read-write` | **Fundamental** | Memory axiom 1 |
| Encoding.agda | `mem-read-other` | **Fundamental** | Memory axiom 2 |
| Encoding.agda | `encode-injective` | **Fundamental** | Memory axiom 3 |
| Encoding.agda | `encode-is-alloc-addr-pair` | **Fundamental** | Connection axiom |
| Star.agda | `exec-to-star` | Plumbing | Bridge lemma |
| Star.agda | `exec-until-pc-to-star` | Plumbing | Bridge lemma |
| Correct.agda | `closure-code-ptr-x86` | Runtime | Closure support |
| Correct.agda | `run-apply-seq` | Runtime | Closure application |
| Correct.agda | `postulate-pc-at-fuel-zero` | Edge case | Rarely hit |

**Eliminated this session:**
- ✅ `∸+<-lemma` - proven using standard library
- ✅ `exec-until-pc-to-exec` - deleted (was unused)

---

## The No-`with` Rule

**`with` is banned everywhere.**

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
