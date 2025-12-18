# X86 Backend Verification Architecture

## The 3-Axiom Foundation

The entire X86 verification rests on **exactly 3 axioms**:

```agda
postulate
  -- 1. Encoding is injective (distinct values → distinct words)
  encode-injective : encode x ≡ encode y → x ≡ y

  -- 2. Memory read-after-write (same address)
  mem-read-write : readMem (writeMem m addr v) addr ≡ just v

  -- 3. Memory frame (different address)
  mem-read-other : addr₁ ≢ addr₂ → readMem (writeMem m addr₁ v) addr₂ ≡ readMem m addr₂
```

**Everything else is derived** from these 3 axioms + computable semantics.

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

The current ~15 encoding axioms like `encode-pair-fst`, `encode-inl-tag`, etc. should be **derived** from:

1. **Concrete `encode` definition** for each type
2. **The 3 memory axioms**

### Example: Pair Encoding

```agda
-- Define encode concretely
encode {A * B} (a , b) = allocPair (encode a) (encode b)

-- Derive properties from memory axioms
encode-pair-fst : readMem m (encode (a , b)) ≡ just (encode a)
encode-pair-fst = mem-read-write  -- by construction of allocPair

encode-pair-snd : readMem m (encode (a , b) + 8) ≡ just (encode b)
encode-pair-snd = mem-read-write  -- second slot
```

---

## Verification Commands

```bash
# Per-file typecheck (use during development)
make agda MODULE=Once/Backend/X86/Semantics.agda
make agda MODULE=Once/Backend/X86/Correct.agda

# Full X86 backend
make x86-correct
```

---

## Success Criteria

- [ ] Only 3 postulates in the entire X86 verification
- [ ] `make agda MODULE=Once/Backend/X86/Semantics.agda` passes
- [ ] `make agda MODULE=Once/Backend/X86/Correct.agda` passes
- [ ] `make x86-correct` passes
- [ ] No `with` anywhere in X86 backend files
