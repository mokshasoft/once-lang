# CCC Normalizer Verification

This directory contains the Agda verification of a CCC (Cartesian Closed Category)
normalizer. The key result is that the normalizer achieves a fixpoint on its own
encoding - proven entirely without postulates.

## Directory Structure

```
normalizer/
├── Syntax/              # Core type definitions
│   ├── Types.agda       # Minimal prelude, Ty, Func, decidable equality
│   ├── CCC.agda         # Term, reduction relations, parallel reduction
│   ├── NoRedex.agda     # Definition of redex-free terms
│   ├── NormalForm.agda  # Normal form definitions
│   └── BetaNormalForm.agda  # Beta-normal form, encode-is-betanf
│
├── Encoding/            # Self-representation infrastructure
│   ├── Encoding.agda    # Term encoding ⌜_⌝, TyFuncCode, TermCode'
│   ├── TermFunctor.agda # TermF decomposition for proofs
│   └── Catamorphisms.agda # Generic catamorphism lemmas
│
├── Combinators/         # Proof infrastructure
│   ├── Chain.agda       # Re-exports for proof chains
│   ├── ReductionCombinators.agda  # _>>_, ⟶1 operators
│   ├── DispatchCombinators.agda   # Lemmas for position dispatch
│   └── OutIn.agda       # Out/In composition lemmas
│
├── Axioms/              # Postulates (established math)
│   ├── EstablishedMath.agda  # Strong normalization, confluence
│   └── Confluence.agda       # Diamond property derivation
│
├── TCB0/                # POSTULATE-FREE proofs (Trusted Computing Base)
│   ├── Normalizer/
│   │   ├── Definition.agda   # normalize = cata TermF normalize-step
│   │   ├── Handlers.agda     # Handler functions for each position
│   │   ├── Dispatch.agda     # is-id and other tag dispatchers
│   │   ├── Rebuild.agda      # rebuild-N helper functions
│   │   ├── NoRedexProof.agda # Re-export of NoRedex definitions
│   │   ├── NoRedexFixpoint.agda  # fixpoint-property theorem
│   │   ├── SelfFixpoint.agda     # noredex-fixpoint by induction
│   │   └── Proofs/           # Supporting lemmas
│   ├── Compiler/
│   │   └── SatisfiesSpec.agda  # Proof that algebra satisfies spec
│   └── RefoldIdempotent.agda   # (cata TermF In ∘ encode t) ⟶* encode t
│
├── Theory/              # Postulate-dependent theoretical results
│   ├── Spec/
│   │   ├── NormalizerSpec.agda  # Specification record
│   │   └── AlgebraSpec.agda     # Per-position conditions
│   ├── GeneralCorrectness/      # Parameterized correctness proofs
│   │   ├── Correctness.agda
│   │   ├── Record.agda
│   │   ├── Preserves.agda
│   │   ├── ProducesNF.agda
│   │   └── Terminates.agda
│   └── FixpointTheorem.agda     # Beta-normal form implications
│
├── Testing/             # Empirical verification
│   ├── Evaluator.agda   # Interpret CCC terms as Agda functions
│   └── RunTest.agda     # Type-level fixpoint test
│
├── TCB0.agda            # Entry point: postulate-free proofs
└── Main.agda            # Entry point: full theorem with postulates
```

## Key Theorems

### TCB0 (Postulate-Free)

The core verification is entirely postulate-free:

```agda
-- The normalizer achieves fixpoint on its own encoding
fixpoint-property : (normalize ∘ encode normalize) ⟶* encode normalize

-- More generally, for any term without redexes
noredex-fixpoint : ∀ t → NoRedex t → (normalize ∘ encode t) ⟶* encode t
```

### Full Theory (Uses Postulates)

With established mathematical results (strong normalization, confluence):

```agda
-- Encodings are in beta-normal form
encode-is-betanf : ∀ t → IsBetaNormalForm (encode t)

-- The normalizer encoding is beta-stable
normalize-encoded-is-betanf : IsBetaNormalForm normalize-encoded
```

## Building

```bash
# Verify postulate-free core (recommended)
make tcb0

# Verify full theorem (requires accepting postulates)
make main

# Run all checks
make all

# See all targets
make help
```

## The CCC IR

The complete CCC with:
- Identity and composition: `id`, `∘`
- Products: `fst`, `snd`, `⟨_,_⟩`
- Coproducts: `inl`, `inr`, `[_,_]`
- Exponentials: `curry`, `apply`
- Initial/terminal: `initial`, `terminal`
- Inductive types: `In`, `Out`, `cata`

## Verification Strategy

The verification uses the "shortcut" approach:

1. **Direct NoRedex proof**: Show `normalize-step` produces `NoRedex` output
2. **Structural induction**: Prove `noredex-fixpoint` for all `NoRedex` terms
3. **Self-application**: Apply to `encode normalize` (which is `NoRedex`)

This bypasses the need for strong normalization in the core proof.
