------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.Diamond
--
-- Complete development _* for the FULL βη rule set at CCT1.
--
-- Defines _* as the canonical "fire-all-visible-redexes" function over
-- terms. Each shape is tested in priority order:
--   β-rules first  (id-left, fst-pair, snd-pair, curry-β, id-right)
--   η-rules next   (curry-compose, curry-η, curry-apply)
--   s-rules last   (assoc, pair-dist, term-unique)
--   catch-all      (structural recursion on subterms)
--
-- ETA-PAIR-GEN LIMITATION:
--   eta-pair-gen has a non-linear LHS pattern ⟨ fst ∘ h , snd ∘ h ⟩
--   (the SAME h on both sides). Linear pattern matching cannot fire it
--   without decidable Term equality. _* leaves eta-pair-gen redexes
--   unfired; the diamond / confluence proofs that consume _* will
--   need a Hindley-Rosen-style side argument for that one rule, or a
--   refined _* using decidable Term equality.
--
-- LEMMA 1 (t ⟹ t*) is the immediate next milestone; deferred to a
-- subsequent commit because the case enumeration interacts subtly
-- with the f-id pattern (id-right) — every non-atomic LHS needs g
-- enumerated to disambiguate id-right from the s/η rules — and the
-- type-compatibility constraints inside curry-⟹-* are intricate
-- (many `apply ∘ ⟨ left , right ⟩` patterns that look reasonable
-- linguistically are type-impossible).
--
-- ZERO POSTULATES.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.Diamond where

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.StrongCCL.CCT1.ParallelReduction

------------------------------------------------------------------------
-- Complete development _*
------------------------------------------------------------------------

mutual
  _* : ∀ {A B} → Term A B → Term A B
  id *        = id
  terminal *  = terminal
  fst *       = fst
  snd *       = snd
  apply *     = apply
  (f ∘ g) *   = compose-* f g
  ⟨ f , g ⟩ * = pair-* f g
  (curry f) * = curry-* f

  -- compose-*: tests (LHS, RHS) for redex membership in priority order.
  --   β-rules first (id-left, fst-pair, snd-pair, curry-β, id-right)
  --   then η-rule (curry-compose), then s-rules (assoc, pair-dist,
  --   term-unique), then catch-all.
  compose-* : ∀ {A B C} → Term B C → Term A B → Term A C
  compose-* id        g                = g *                                 -- id-left
  compose-* fst       ⟨ h , k ⟩        = h *                                 -- fst-pair
  compose-* snd       ⟨ h , k ⟩        = k *                                 -- snd-pair
  compose-* apply     ⟨ curry h , k ⟩  = (h *) ∘ ⟨ id , k * ⟩                -- curry-β
  compose-* f         id               = f *                                 -- id-right
  compose-* (curry h) g                = curry ((h *) ∘ ⟨ (g *) ∘ fst , snd ⟩) -- curry-compose
  compose-* (h ∘ k)   g                = (h *) ∘ ((k *) ∘ (g *))             -- assoc
  compose-* ⟨ h , k ⟩ g                = ⟨ (h *) ∘ (g *) , (k *) ∘ (g *) ⟩   -- pair-dist
  compose-* terminal  g                = terminal                            -- term-unique
  compose-* f         g                = (f *) ∘ (g *)                       -- catch-all

  pair-* : ∀ {A B C} → Term C A → Term C B → Term C (A × B)
  pair-* fst snd = id  -- eta-pair
  -- eta-pair-gen NOT fired here (non-linear LHS).
  pair-* f   g   = ⟨ f * , g * ⟩

  curry-* : ∀ {A B C} → Term (A × B) C → Term A (B ⇒ C)
  curry-* apply                              = id    -- curry-apply
  curry-* (apply ∘ ⟨ h ∘ fst , snd ⟩)        = h *   -- curry-η
  curry-* f                                  = curry (f *)
