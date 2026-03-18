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
--   6. apply ∘ ⟨ f , x ⟩ m → apply ∘ ⟨ f , x ⟩ Stack  (pair consumed by apply)
--      (generalizes rule 5 for non-curry functions)
--   7. fold ∘ inl m → fold ∘ inl Stack  (injection consumed by fold)
--   8. fold ∘ inr m → fold ∘ inr Stack  (injection consumed by fold)
--   9. terminal ∘ ⟨ f , g ⟩ m → terminal ∘ ⟨ f , g ⟩ Stack  (pair discarded)
--  10. terminal ∘ curry f m → terminal ∘ curry f Stack  (closure discarded)
--  11. (f ∘ fst) ∘ ⟨ g , h ⟩ m → (f ∘ fst) ∘ ⟨ g , h ⟩ Stack  (pair consumed by fst)
--  12. (f ∘ snd) ∘ ⟨ g , h ⟩ m → (f ∘ snd) ∘ ⟨ g , h ⟩ Stack  (pair consumed by snd)
--
-- Rules 7-8 are especially powerful with linear types: linearity guarantees
-- the injection is used exactly once, so stack allocation is provably safe.
-- Rules 9-10 are edge cases for dead code that wasn't eliminated.
-- Rules 11-12 are high-impact for let bindings: `let x = e1 in f x` desugars to
-- `(f ∘ snd) ∘ ⟨id, e1⟩` which is now optimized.
------------------------------------------------------------------------

module Once.Escape where

open import Once.Type
open import Once.CCC.IR

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
escape-compose (case f g) (inl _) = (case f g) ∘ inl Stack

-- Rule 4: [ f , g ] ∘ inr m → [ f , g ] ∘ inr Stack
-- The right injection is immediately consumed by case analysis.
escape-compose (case f g) (inr _) = (case f g) ∘ inr Stack

-- Rule 5: apply ∘ ⟨ curry f m₁ , x ⟩ m₂ → apply ∘ ⟨ curry f Stack , x ⟩ Stack
-- The closure is immediately applied, and the argument pair is immediately
-- consumed by apply. Neither the closure nor the pair escape.
escape-compose apply (⟨ curry {q = q} f _ , x ⟩ _) = apply ∘ ⟨ curry {q = q} f Stack , x ⟩ Stack

-- Rule 6: apply ∘ ⟨ f , x ⟩ m → apply ∘ ⟨ f , x ⟩ Stack (for non-curry f)
-- The pair is immediately consumed by apply, regardless of how f produces
-- the function. This generalizes rule 5 to all function-producing terms.
escape-compose apply (⟨ id , x ⟩ _) = apply ∘ ⟨ id , x ⟩ Stack
escape-compose apply (⟨ g ∘ h , x ⟩ _) = apply ∘ ⟨ g ∘ h , x ⟩ Stack
escape-compose apply (⟨ fst , x ⟩ _) = apply ∘ ⟨ fst , x ⟩ Stack
escape-compose apply (⟨ snd , x ⟩ _) = apply ∘ ⟨ snd , x ⟩ Stack
escape-compose apply (⟨ (case f g) , x ⟩ _) = apply ∘ ⟨ (case f g) , x ⟩ Stack
escape-compose (apply {q = q}) (⟨ initial , x ⟩ _) = apply {q = q} ∘ ⟨ initial , x ⟩ Stack
escape-compose (apply {q = q₁}) (⟨ apply {q = q₂} , x ⟩ _) = apply {q = q₁} ∘ ⟨ apply {q = q₂} , x ⟩ Stack
escape-compose (apply {q = q}) (⟨ Prim name , x ⟩ _) = apply {q = q} ∘ ⟨ Prim name , x ⟩ Stack

-- Rule 7: fold ∘ inl m → fold ∘ inl Stack
-- The left injection is immediately consumed by fold to construct a Fix value.
-- Common pattern: nil = (fold Heap) ∘ inl (for list-like structures)
-- With linear types, the injection is guaranteed to be used exactly once.
escape-compose (fold _) (inl _) = (fold Heap) ∘ inl Stack

-- Rule 8: fold ∘ inr m → fold ∘ inr Stack
-- The right injection is immediately consumed by fold to construct a Fix value.
-- Common pattern: cons = (fold Heap) ∘ inr (for list-like structures)
-- With linear types, the injection is guaranteed to be used exactly once.
escape-compose (fold _) (inr _) = (fold Heap) ∘ inr Stack

-- Rules 9-10: terminal discards values (edge cases for dead code)
escape-compose terminal (⟨ f , g ⟩ _) = terminal ∘ ⟨ f , g ⟩ Stack
escape-compose terminal (curry {q = q} f _) = terminal ∘ curry {q = q} f Stack

-- Rules 11-12: (f ∘ fst/snd) ∘ ⟨ g , h ⟩ - projection inside composition
-- The pair is consumed by the projection, even when followed by another function.
-- This is HIGH IMPACT for let bindings: `let x = e in f x` → `(f ∘ snd) ∘ ⟨id, e⟩`
escape-compose (f ∘ fst) (⟨ g , h ⟩ _) = (f ∘ fst) ∘ ⟨ g , h ⟩ Stack
escape-compose (f ∘ snd) (⟨ g , h ⟩ _) = (f ∘ snd) ∘ ⟨ g , h ⟩ Stack

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
escape-once (case f g) = case (escape-once f) (escape-once g)

-- Terminal/Initial: no allocation
escape-once terminal = terminal
escape-once initial = initial

-- Curry: recurse into body, preserve mode
-- (Mode may be optimized when this closure is consumed in a composition)
escape-once (curry {q = q} f m) = curry {q = q} (escape-once f) m

-- Apply: no allocation in apply itself
escape-once apply = apply

-- Fixed points: no allocation
escape-once (fold _) = fold Heap
escape-once unfold = unfold

-- Effects: no allocation
escape-once arr = arr

-- Primitives: opaque, pass through
escape-once (Prim name) = Prim name

-- free-heap: opaque, pass through
escape-once (free-heap h) = free-heap h

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
