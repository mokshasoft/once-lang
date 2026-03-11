# Once Bootstrap: Minimal-Trust Verification

This directory contains the bootstrap infrastructure for Once's minimal-trust
verification system, as specified in OCP-0004.

## Trust Architecture

```
TCB (Trusted Computing Base - ~212 lines, human-verified)
├── tcb/scheme.c        (~200 lines) - Minimal Scheme interpreter
└── tcb/verifier.scm    (~12 lines)  - Trace verifier

UNTRUSTED (verified by TCB)
└── normalizer/         - Produces traces checked by verifier
```

## How It Works

1. The **verifier** checks that reduction traces are valid applications of categorical laws
2. The **normalizer** produces traces (but we don't trust it - traces are verified)
3. The **bootstrap** uses this to verify the Once verifier, enabling self-hosting

## Quick Start

```bash
./bootstrap.sh
```

## The Categorical Laws

The verifier checks these reduction rules (the definition of a CCC):

```
Identity:     compose f id → f
              compose id f → f

Products:     fst ∘ pair f g → f
              snd ∘ pair f g → g
              pair fst snd → id

Coproducts:   case f g ∘ inl → f
              case f g ∘ inr → g
              case inl inr → id

Exponential:  apply ∘ pair (curry f) id → f
```

## Directory Structure

- `tcb/` - Trusted Computing Base (must be human-verified)
- `normalizer/` - Untrusted normalizer (verified by output)
- `spec/` - Mathematical specification
- `traces/` - Generated reduction traces

## See Also

- `docs/proposals/OCP-0004-zero-trust-verification.md` - Full specification
- `docs/proposals/OCP-0003-total-productive-ir.md` - IR architecture
