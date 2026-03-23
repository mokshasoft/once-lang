------------------------------------------------------------------------
-- ReductionCombinators: Lightweight reduction proof combinators
--
-- This module provides operator syntax for chaining reduction proofs
-- without pulling in heavy dependencies.
------------------------------------------------------------------------

module normalizer.Combinators.ReductionCombinators where

open import normalizer.Syntax.CCC
  using (Ty; Term; _⟶_; _⟶*_; step; done; ⟶*-trans)
  public

------------------------------------------------------------------------
-- Flat chain combinator
------------------------------------------------------------------------

infixr 5 _>>_

_>>_ : ∀ {A B} {t u v : Term A B} → t ⟶* u → u ⟶* v → t ⟶* v
_>>_ = ⟶*-trans

------------------------------------------------------------------------
-- Single step wrapper
------------------------------------------------------------------------

⟶1 : ∀ {A B} {t u : Term A B} → t ⟶ u → t ⟶* u
⟶1 r = step r done

------------------------------------------------------------------------
-- Chain: Explicit intermediate terms for reduction proofs
--
-- Instead of nested ⟶*-trans with inferred intermediates:
--   ⟶*-trans p1 (⟶*-trans p2 (⟶*-trans p3 done))
--
-- Use explicit chain with named intermediate terms:
--   t1 ∵ p1 ⟶ t2 ∵ p2 ⟶ t3 ∵ p3 ⟶ t4 ∎
--
-- Benefits:
-- 1. No type inference for intermediate terms
-- 2. Each step type-checks independently
-- 3. Better error messages
------------------------------------------------------------------------

infixr 2 _∵_⟶_
infix 3 _∎

-- Chain with explicit intermediate terms
data Chain {A B : Ty} : Term A B → Term A B → Set where
  _∎ : (t : Term A B) → Chain t t
  _∵_⟶_ : (t : Term A B) → ∀ {u v} → t ⟶* u → Chain u v → Chain t v

-- Convert chain to reduction proof
runChain : ∀ {A B} {t u : Term A B} → Chain t u → t ⟶* u
runChain (t ∎) = done
runChain (t ∵ p ⟶ rest) = ⟶*-trans p (runChain rest)
