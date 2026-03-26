# Paramorphism and Bounded Hylomorphism

## The Problem

The current `Hylo` construct has a `{-# TERMINATING #-}` pragma in its semantic
implementation (`sem-hylo` in `Once.Semantics.Core`). This is a trust-me pragma
that tells Agda to accept termination without proof.

The issue: a general hylomorphism `hylo alg coalg` can diverge if the coalgebra
never produces base cases. For example:

```agda
-- This diverges: coalgebra always produces recursive structure
divergingCoalg : Unit → ⟦ NatF ⟧F Unit
divergingCoalg tt = inj₂ tt  -- Always "suc", never "zero"

divergingHylo = sem-hylo NatF (λ _ → tt) divergingCoalg tt  -- loops forever
```

## The Category Theory Solution: Paramorphism

**Paramorphism** is a recursion scheme that provides access to both:
- The recursive results (like Cata)
- The original substructures (unlike Cata)

Type signature:
```
para : (F (μF × A) → A) → μF → A
```

The algebra receives `F (μF × A)` where each position has:
- The original substructure (`μF`)
- The recursive result (`A`)

### Standard Derivation via Cata

Para is derivable from Cata by making the carrier type `μF × A`:

```agda
paraS : ∀ {F} {A : Set} → (⟦ F ⟧SF (μS F × A) → A) → μS F → A
paraS {F} alg x = proj₂ (cataS {F} alg' x)
  where
    alg' : ⟦ F ⟧SF (μS F × A) → (μS F × A)
    alg' fx = (⟨ sfmap F proj₁ fx ⟩ , alg fx)
```

The algebra returns both:
1. The reconstructed `μF` value (via `⟨ sfmap F proj₁ fx ⟩`)
2. The actual result (via `alg fx`)

This is **terminating without any pragma** because Cata is terminating.

## Bounded Hylomorphism via Para

With Para, we can implement fuel-bounded iteration:

```agda
-- State type: (μG × A) where μG is the "fuel"
-- Carrier for Para: A → B (functions from state to result)

boundedHylo : (alg : F B → B)
            → (coalg : G (μG) × A → F (μG × A))
            → (μG × A) → B
boundedHylo alg coalg (fuel, state) = para paraAlg fuel state
  where
    paraAlg : G (μG × (A → B)) → (A → B)
    paraAlg gOfPairs state' =
      let gOfFuel = fmap proj₁ gOfPairs  -- original fuel substructures
          fLayer = coalg (gOfFuel, state')
          -- Apply continuations to recursive positions
          result = fmap (λ (f, s) → lookup f gOfPairs s) fLayer
      in alg result
```

### The `obs` Example

`obs n stream` takes n elements from a stream. Currently implemented via Hylo:

```agda
obs : Nat × Stream A → List A
obs = Hylo wfListF alg coalg
  where
    coalg : (Nat × Stream A) → ListF (Nat × Stream A)
    coalg (n, s) = case (out-μ n) of
      inl tt → inl tt                           -- zero → Nil
      inr k  → inr (head s, (k, tail s))        -- suc k → Cons (head, (k, tail))
```

With Para on NatF:

```agda
obs : Nat × Stream A → List A
obs (fuel, stream) = para paraAlg fuel stream
  where
    -- Para gives us: NatF (Nat × (Stream A → List A))
    -- = Unit + (Nat × (Stream A → List A))
    paraAlg : NatF (Nat × (Stream A → List A)) → (Stream A → List A)
    paraAlg (inl tt) _ = []                    -- zero: empty list
    paraAlg (inr (_, k)) s = head s :: k (tail s)  -- suc: cons head, apply continuation to tail
```

Key insight: in the suc case, we have exactly one continuation `k` and one
recursive call site. The continuation is applied to `tail s`.

**This is terminating by structural recursion on Nat** - no TERMINATING pragma needed!

## When F ≠ G

In `obs`, the fuel functor G = NatF and result functor F = ListF:
- NatF = Unit + X (1 recursive position)
- ListF = Unit + (A × X) (1 recursive position)

They have matching recursive structure: both have 0 positions in the base case
and 1 position in the recursive case.

For the general case where F and G have different numbers of recursive positions,
we need the coalgebra to specify how G-positions map to F-positions. This is more
complex and may require explicit "routing" information.

For practical purposes, the F = G case (or matching recursive structure) covers
most uses:
- `obs` (NatF → ListF, both 0/1 pattern)
- `foldObs` (NatF → any, single position)
- Bounded tree traversals (TreeF → TreeF)

## Implementation Plan

### Phase 1: Add Para to IR and Semantics

1. **Once.CCC.IR**: Add `Para` constructor
   ```agda
   Para : ∀ {F} → WellFormedF F → ∀ {A}
        → IR (⟦ F ⟧T (μ-type F * A) ) A
        → IR (μ-type F) A
   ```

2. **Once.Functor.Base**: Add `paraS` (derived from cataS)
   ```agda
   paraS : ∀ {F} {A : Set} → (⟦ F ⟧SF (μS F × A) → A) → μS F → A
   ```

3. **Once.Semantics.Core**: Add `sem-para` evaluation
   ```agda
   eval ps (Para wf alg) x = sem-para wf (λ fx → eval ps alg (coerce-functor⁻¹ F _ fx)) x
   ```

### Phase 2: Document Hylo Limitations

Keep `Hylo` but document clearly:
- The TERMINATING pragma means termination is trusted, not proven
- Safe alternative: use Para-based bounded recursion
- For cases requiring full Hylo, termination must be argued externally

### Phase 3: Migrate obs to Para

Rewrite `obs` in `Once.Derived.Observation` to use Para:
- Termination becomes provable
- Same computational behavior
- Full fusion still possible (Para is a special case of Cata)

## Benefits

1. **Provable termination**: Para-based bounded hylos terminate by structural recursion
2. **No trust pragmas**: The TERMINATING pragma on sem-hylo is not needed for bounded cases
3. **Same expressiveness**: All practical bounded-observation patterns are covered
4. **Fusion preserved**: Para composes with other schemes for optimization

## Remaining Work

- General Hylo with TERMINATING: document as "expert use only" with external termination argument
- Consider removing general Hylo entirely if all uses can be Para-based
- Investigate if Ana's TERMINATING can also be removed (productivity vs termination)
