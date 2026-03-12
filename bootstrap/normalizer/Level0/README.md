# Level 0 Normalizer

The foundation of the bootstrap tower. This normalizer handles the minimal CCC IR
and is verified purely by the fixpoint property + mathematical theorems.

## IR Operations

- Category: `id`, `_∘_`
- Products: `fst`, `snd`, `⟨_,_⟩`
- Coproducts: `inl`, `inr`, `[_,_]`
- Terminal: `terminal`
- Initial Algebras: `In`, `cata`

## Reduction Rules

```
id ∘ f        ⟶ f           (id-left)
f ∘ id        ⟶ f           (id-right)
fst ∘ ⟨f,g⟩   ⟶ f           (fst-pair)
snd ∘ ⟨f,g⟩   ⟶ g           (snd-pair)
⟨fst,snd⟩     ⟶ id          (eta-pair)
[f,g] ∘ inl   ⟶ f           (case-inl)
[f,g] ∘ inr   ⟶ g           (case-inr)
[inl,inr]     ⟶ id          (eta-case)
cata F a ∘ In ⟶ a ∘ fmap F (cata F a)  (cata-β)
```

## Verification

The normalizer is verified by proving it satisfies `NormalizerSpec`:

1. **N-wf**: Follows from structure (built with `cata`)
2. **N-fixpoint**: The normalizer applied to its own encoding returns the encoding
3. **produces-encoding**: Output is always an encoding (In ∘ ...)
4. **correct-reduction**: Each reduction corresponds to a valid CCC rule

## TCB

After verification, the TCB for Level 0 is:
- Mathematics (categorical laws, Lambek's Lemma)
- Hardware
- Bootstrap code (~50-100 lines, or less with traces)
