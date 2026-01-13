------------------------------------------------------------------------
-- Once.Escape
--
-- Escape analysis for Once IR.
-- Rewrites AllocMode from Heap to Stack where allocations are
-- immediately consumed, making stack allocation safe.
--
-- Key insight: AllocMode is semantically transparent (ignored in eval),
-- so all rewrites are trivially correct. This module identifies patterns
-- where allocations don't escape their immediate context.
--
-- Rules implemented:
--   1. fst ∘ ⟨ f , g ⟩ m → fst ∘ ⟨ f , g ⟩ Stack  (pair consumed by fst)
--   2. snd ∘ ⟨ f , g ⟩ m → snd ∘ ⟨ f , g ⟩ Stack  (pair consumed by snd)
--   3. [ f , g ] ∘ inl m → [ f , g ] ∘ inl Stack  (injection consumed by case)
--   4. [ f , g ] ∘ inr m → [ f , g ] ∘ inr Stack  (injection consumed by case)
--   5. apply ∘ ⟨ curry f m₁ , x ⟩ m₂ → apply ∘ ⟨ curry f Stack , x ⟩ Stack
--      (closure immediately applied, pair immediately consumed)
------------------------------------------------------------------------

module Once.Escape where

open import Once.Type
open import Once.IR

open import Data.Nat using (ℕ; zero; suc)

------------------------------------------------------------------------
-- Escape Analysis: Composition Rules
------------------------------------------------------------------------

-- | Rewrite allocations to Stack where immediately consumed
--
-- These patterns identify where an allocation is created and immediately
-- destructed in the same composition, meaning the value never escapes
-- to the heap and can safely live on the stack.
--
escape-compose : ∀ {A B C} → IR B C → IR A B → IR A C

-- Rule 1: fst ∘ ⟨ f , g ⟩ m → fst ∘ ⟨ f , g ⟩ Stack
-- The pair is created only to immediately extract the first component.
-- The pair value never escapes - it's consumed by fst right away.
escape-compose fst (⟨ f , g ⟩ _) = fst ∘ ⟨ f , g ⟩ Stack

-- Rule 2: snd ∘ ⟨ f , g ⟩ m → snd ∘ ⟨ f , g ⟩ Stack
-- The pair is created only to immediately extract the second component.
escape-compose snd (⟨ f , g ⟩ _) = snd ∘ ⟨ f , g ⟩ Stack

-- Rule 3: [ f , g ] ∘ inl m → [ f , g ] ∘ inl Stack
-- The left injection is immediately consumed by case analysis.
-- The sum value never escapes - it's pattern matched right away.
escape-compose [ f , g ] (inl _) = [ f , g ] ∘ inl Stack

-- Rule 4: [ f , g ] ∘ inr m → [ f , g ] ∘ inr Stack
-- The right injection is immediately consumed by case analysis.
escape-compose [ f , g ] (inr _) = [ f , g ] ∘ inr Stack

-- Rule 5: apply ∘ ⟨ curry f m₁ , x ⟩ m₂ → apply ∘ ⟨ curry f Stack , x ⟩ Stack
-- The closure is immediately applied, and the argument pair is immediately
-- consumed by apply. Neither the closure nor the pair escape.
escape-compose apply (⟨ curry f _ , x ⟩ _) = apply ∘ ⟨ curry f Stack , x ⟩ Stack

-- Default: no escape optimization, preserve original composition
escape-compose g f = g ∘ f

------------------------------------------------------------------------
-- Escape Analysis: Single Pass
------------------------------------------------------------------------

-- | Apply escape analysis recursively to an IR term
--
-- Descend into all subterms, applying escape-compose at composition
-- points to identify stack-allocatable values.
--
escape-once : ∀ {A B} → IR A B → IR A B

-- Identity: nothing to optimize
escape-once id = id

-- Composition: the key case - recurse into both sides, then apply rules
escape-once (g ∘ f) = escape-compose (escape-once g) (escape-once f)

-- Projections: no allocation, pass through
escape-once fst = fst
escape-once snd = snd

-- Pairing: recurse into components, preserve mode
-- (Mode may be optimized when this pair is consumed in a composition)
escape-once (⟨ f , g ⟩ m) = ⟨ escape-once f , escape-once g ⟩ m

-- Injections: preserve mode
-- (Mode may be optimized when this injection is consumed in a composition)
escape-once (inl m) = inl m
escape-once (inr m) = inr m

-- Case: recurse into branches
escape-once [ f , g ] = [ escape-once f , escape-once g ]

-- Terminal/Initial: no allocation
escape-once terminal = terminal
escape-once initial = initial

-- Curry: recurse into body, preserve mode
-- (Mode may be optimized when this closure is consumed in a composition)
escape-once (curry f m) = curry (escape-once f) m

-- Apply: no allocation in apply itself
escape-once apply = apply

-- Fixed points: no allocation
escape-once fold = fold
escape-once unfold = unfold

-- Effects: no allocation
escape-once arr = arr

-- Primitives: opaque, pass through
escape-once (Prim name) = Prim name

------------------------------------------------------------------------
-- Escape Analysis: Bounded Iteration
------------------------------------------------------------------------

-- | Apply escape analysis n times
--
-- Multiple passes may find new opportunities as the IR is rewritten.
--
escape-n : ∀ {A B} → ℕ → IR A B → IR A B
escape-n zero ir = ir
escape-n (suc n) ir = escape-n n (escape-once ir)

-- | Main entry point: apply escape analysis with fixed bound
--
-- 10 iterations should be sufficient for most programs.
--
escape : ∀ {A B} → IR A B → IR A B
escape = escape-n 10
