------------------------------------------------------------------------
-- normalizer.Theory.Eval.CataTerminates
--
-- De-risking the operational evaluator's TOTALITY: the only obligation is
-- that the catamorphism fold terminates. Testing.Evaluator.cata-Set
-- currently asserts this with a {-# TERMINATING #-} pragma. Here we give
-- the PROVEN version: a structurally-recursive mutual definition
-- (cata / map-cata) that Agda's termination checker accepts WITHOUT any
-- pragma. If this checks, totality is rigorous (no pragma, no postulate),
-- so the operational-evaluator route is sound on its hardest obligation.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/CataTerminates.agda
------------------------------------------------------------------------

module normalizer.Theory.Eval.CataTerminates where

open import normalizer.Syntax.Types
  using (Func; Id; K; _⊕_; _⊗_; inj₁; inj₂; _,_)
open import normalizer.Testing.Evaluator using (⟦_⟧FS; Fix; fix)

------------------------------------------------------------------------
-- Structural catamorphism — NO {-# TERMINATING #-}.
--
-- `cata` recurses on the Fix argument (fix x ↦ x), and `map-cata`
-- recurses on the functor code (G ⊕/⊗ H ↦ G, H) until `Id`, where it
-- calls `cata` on a strictly-smaller sub-Fix. Agda accepts this mutual
-- structural descent.
------------------------------------------------------------------------

mutual
  cata : ∀ F {A : Set} → (⟦ F ⟧FS A → A) → Fix F → A
  cata F alg (fix x) = alg (map-cata F F alg x)

  map-cata : ∀ F G {A : Set} →
             (⟦ F ⟧FS A → A) → ⟦ G ⟧FS (Fix F) → ⟦ G ⟧FS A
  map-cata F Id      alg y        = cata F alg y
  map-cata F (K _)   alg y        = y
  map-cata F (G ⊕ H) alg (inj₁ y) = inj₁ (map-cata F G alg y)
  map-cata F (G ⊕ H) alg (inj₂ z) = inj₂ (map-cata F H alg z)
  map-cata F (G ⊗ H) alg (y , z)  = map-cata F G alg y , map-cata F H alg z
