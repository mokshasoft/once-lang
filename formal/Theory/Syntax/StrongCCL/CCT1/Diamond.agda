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
  -- eta-pair-gen ⟨ fst ∘ h , snd ∘ h ⟩ ⟶s h: tried with the
  -- DecidableEquality lemmas via Dec-as-arg helpers (no `with` clause
  -- in the mutual block), but Agda's termination check still flags
  -- the recursive `compose-* fst h₁` call inside the Dec helper as
  -- non-decreasing — the chain pair-* → pair-eta-gen-Ty-dec →
  -- compose-* loses h₁'s structural-subterm relationship with the
  -- pair-* input across the helper boundary.
  --
  -- Closing this needs either:
  --   (a) sized types or an explicit Acc-on-term-size argument
  --       through the mutual block (substantial refactor);
  --   (b) parametrising the helper with _* and compose-* as
  --       higher-order arguments (clean conceptually but breaks
  --       Agda's first-order termination heuristic).
  -- Both are their own focused projects.  Integration deferred.
  pair-* f   g   = ⟨ f * , g * ⟩

  curry-* : ∀ {A B C} → Term (A × B) C → Term A (B ⇒ C)
  curry-* apply                              = id    -- curry-apply
  curry-* (apply ∘ ⟨ h ∘ fst , snd ⟩)        = h *   -- curry-η
  curry-* f                                  = curry (f *)

------------------------------------------------------------------------
-- Lemma 1: t ⟹ t*
--
-- Each term reduces in parallel to its complete development. Mutually
-- recursive: top-level dispatch + per-shape helpers for compositions,
-- pairs, and curries.
------------------------------------------------------------------------

⟹-to-*      : ∀ {A B} (t : Term A B) → t ⟹ t *
compose-⟹-* : ∀ {A B C} (f : Term B C) (g : Term A B) →
               (f ∘ g) ⟹ compose-* f g
pair-⟹-*    : ∀ {A B C} (f : Term C A) (g : Term C B) →
               ⟨ f , g ⟩ ⟹ pair-* f g
curry-⟹-*   : ∀ {A B C} (f : Term (A × B) C) →
               curry f ⟹ curry-* f

⟹-to-* id          = ⟹-id
⟹-to-* terminal    = ⟹-terminal
⟹-to-* fst         = ⟹-fst
⟹-to-* snd         = ⟹-snd
⟹-to-* apply       = ⟹-apply
⟹-to-* (f ∘ g)     = compose-⟹-* f g
⟹-to-* ⟨ f , g ⟩   = pair-⟹-* f g
⟹-to-* (curry f)   = curry-⟹-* f

------------------------------------------------------------------------
-- compose-⟹-* — enumerated to disambiguate compose-*'s overlapping
-- patterns (specifically, the `f id` clause for id-right vs the η/s
-- rules for non-id RHS).
------------------------------------------------------------------------

-- LHS = id: id-left fires for any RHS.
compose-⟹-* id g = ⟹-id-left (⟹-to-* g)

-- LHS = fst: fst-pair (RHS=⟨,⟩), id-right (RHS=id), catch-all otherwise.
-- fst : Term (A × B) A, so RHS target must be product (A × B).
-- terminal/curry impossible (Unit/arrow ≠ product).
compose-⟹-* fst ⟨ h , k ⟩ = ⟹-fst-β (⟹-to-* h) (⟹-to-* k)
compose-⟹-* fst id        = ⟹-id-right ⟹-fst
compose-⟹-* fst fst       = ⟹-∘ ⟹-fst ⟹-fst
compose-⟹-* fst snd       = ⟹-∘ ⟹-fst ⟹-snd
compose-⟹-* fst apply     = ⟹-∘ ⟹-fst ⟹-apply
compose-⟹-* fst (h ∘ k)   = ⟹-∘ ⟹-fst (compose-⟹-* h k)

-- LHS = snd: symmetric to fst.
compose-⟹-* snd ⟨ h , k ⟩ = ⟹-snd-β (⟹-to-* h) (⟹-to-* k)
compose-⟹-* snd id        = ⟹-id-right ⟹-snd
compose-⟹-* snd fst       = ⟹-∘ ⟹-snd ⟹-fst
compose-⟹-* snd snd       = ⟹-∘ ⟹-snd ⟹-snd
compose-⟹-* snd apply     = ⟹-∘ ⟹-snd ⟹-apply
compose-⟹-* snd (h ∘ k)   = ⟹-∘ ⟹-snd (compose-⟹-* h k)

-- LHS = apply: curry-β (RHS=⟨curry _, _⟩), id-right (RHS=id), catch-all.
-- apply : Term ((A ⇒ B) × A) B, so RHS target must be product
-- ((A ⇒ B) × A). For ⟨h, k⟩ at this position, h target = A ⇒ B (arrow);
-- ⟨,⟩, terminal at h-position type-impossible.
compose-⟹-* apply ⟨ curry h , k ⟩ = ⟹-curry-β (⟹-to-* h) (⟹-to-* k)
compose-⟹-* apply id              = ⟹-id-right ⟹-apply
compose-⟹-* apply fst             = ⟹-∘ ⟹-apply ⟹-fst
compose-⟹-* apply snd             = ⟹-∘ ⟹-apply ⟹-snd
compose-⟹-* apply apply           = ⟹-∘ ⟹-apply ⟹-apply
compose-⟹-* apply (h ∘ k)         = ⟹-∘ ⟹-apply (compose-⟹-* h k)
compose-⟹-* apply ⟨ id , k ⟩      = ⟹-∘ ⟹-apply (pair-⟹-* id k)
compose-⟹-* apply ⟨ fst , k ⟩     = ⟹-∘ ⟹-apply (pair-⟹-* fst k)
compose-⟹-* apply ⟨ snd , k ⟩     = ⟹-∘ ⟹-apply (pair-⟹-* snd k)
compose-⟹-* apply ⟨ apply , k ⟩   = ⟹-∘ ⟹-apply (pair-⟹-* apply k)
compose-⟹-* apply ⟨ (h ∘ j) , k ⟩ = ⟹-∘ ⟹-apply (pair-⟹-* (h ∘ j) k)

-- LHS = terminal: term-unique fires for non-id RHS, id-right for id.
compose-⟹-* terminal id           = ⟹-id-right ⟹-terminal
compose-⟹-* terminal fst          = ⟹-term-unique
compose-⟹-* terminal snd          = ⟹-term-unique
compose-⟹-* terminal terminal     = ⟹-term-unique
compose-⟹-* terminal apply        = ⟹-term-unique
compose-⟹-* terminal (h ∘ k)      = ⟹-term-unique
compose-⟹-* terminal ⟨ h , k ⟩    = ⟹-term-unique
compose-⟹-* terminal (curry h)    = ⟹-term-unique

-- LHS = (h ∘ k): id-right for RHS=id, assoc otherwise.
compose-⟹-* (h ∘ k) id           = ⟹-id-right (compose-⟹-* h k)
compose-⟹-* (h ∘ k) terminal     = ⟹-assoc (⟹-to-* h) (⟹-to-* k) ⟹-terminal
compose-⟹-* (h ∘ k) fst          = ⟹-assoc (⟹-to-* h) (⟹-to-* k) ⟹-fst
compose-⟹-* (h ∘ k) snd          = ⟹-assoc (⟹-to-* h) (⟹-to-* k) ⟹-snd
compose-⟹-* (h ∘ k) apply        = ⟹-assoc (⟹-to-* h) (⟹-to-* k) ⟹-apply
compose-⟹-* (h ∘ k) (h' ∘ k')    = ⟹-assoc (⟹-to-* h) (⟹-to-* k) (compose-⟹-* h' k')
compose-⟹-* (h ∘ k) ⟨ h' , k' ⟩  = ⟹-assoc (⟹-to-* h) (⟹-to-* k) (pair-⟹-* h' k')
compose-⟹-* (h ∘ k) (curry h')   = ⟹-assoc (⟹-to-* h) (⟹-to-* k) (curry-⟹-* h')

-- LHS = ⟨h, k⟩: id-right for RHS=id, pair-dist otherwise.
compose-⟹-* ⟨ h , k ⟩ id           = ⟹-id-right (pair-⟹-* h k)
compose-⟹-* ⟨ h , k ⟩ terminal     = ⟹-pair-dist (⟹-to-* h) (⟹-to-* k) ⟹-terminal
compose-⟹-* ⟨ h , k ⟩ fst          = ⟹-pair-dist (⟹-to-* h) (⟹-to-* k) ⟹-fst
compose-⟹-* ⟨ h , k ⟩ snd          = ⟹-pair-dist (⟹-to-* h) (⟹-to-* k) ⟹-snd
compose-⟹-* ⟨ h , k ⟩ apply        = ⟹-pair-dist (⟹-to-* h) (⟹-to-* k) ⟹-apply
compose-⟹-* ⟨ h , k ⟩ (h' ∘ k')    = ⟹-pair-dist (⟹-to-* h) (⟹-to-* k) (compose-⟹-* h' k')
compose-⟹-* ⟨ h , k ⟩ ⟨ h' , k' ⟩  = ⟹-pair-dist (⟹-to-* h) (⟹-to-* k) (pair-⟹-* h' k')
compose-⟹-* ⟨ h , k ⟩ (curry h')   = ⟹-pair-dist (⟹-to-* h) (⟹-to-* k) (curry-⟹-* h')

-- LHS = curry h: id-right for RHS=id, curry-compose otherwise.
compose-⟹-* (curry h) id           = ⟹-id-right (curry-⟹-* h)
compose-⟹-* (curry h) terminal     = ⟹-curry-compose (⟹-to-* h) ⟹-terminal
compose-⟹-* (curry h) fst          = ⟹-curry-compose (⟹-to-* h) ⟹-fst
compose-⟹-* (curry h) snd          = ⟹-curry-compose (⟹-to-* h) ⟹-snd
compose-⟹-* (curry h) apply        = ⟹-curry-compose (⟹-to-* h) ⟹-apply
compose-⟹-* (curry h) (h' ∘ k')    = ⟹-curry-compose (⟹-to-* h) (compose-⟹-* h' k')
compose-⟹-* (curry h) ⟨ h' , k' ⟩  = ⟹-curry-compose (⟹-to-* h) (pair-⟹-* h' k')
compose-⟹-* (curry h) (curry h')   = ⟹-curry-compose (⟹-to-* h) (curry-⟹-* h')

------------------------------------------------------------------------
-- pair-⟹-* — enumerate (LHS, RHS) for the pair-* dispatch.
-- eta-pair fires only at (fst, snd); other shapes use catch-all.
------------------------------------------------------------------------

pair-⟹-* fst snd        = ⟹-eta-pair
pair-⟹-* fst id         = ⟹-⟨,⟩ ⟹-fst ⟹-id
pair-⟹-* fst fst        = ⟹-⟨,⟩ ⟹-fst ⟹-fst
pair-⟹-* fst terminal   = ⟹-⟨,⟩ ⟹-fst ⟹-terminal
pair-⟹-* fst apply      = ⟹-⟨,⟩ ⟹-fst ⟹-apply
pair-⟹-* fst (h ∘ k)    = ⟹-⟨,⟩ ⟹-fst (compose-⟹-* h k)
pair-⟹-* fst ⟨ h , k ⟩  = ⟹-⟨,⟩ ⟹-fst (pair-⟹-* h k)
pair-⟹-* fst (curry h)  = ⟹-⟨,⟩ ⟹-fst (curry-⟹-* h)

pair-⟹-* id        g = ⟹-⟨,⟩ ⟹-id (⟹-to-* g)
pair-⟹-* terminal  g = ⟹-⟨,⟩ ⟹-terminal (⟹-to-* g)
pair-⟹-* snd       g = ⟹-⟨,⟩ ⟹-snd (⟹-to-* g)
pair-⟹-* apply     g = ⟹-⟨,⟩ ⟹-apply (⟹-to-* g)
pair-⟹-* (h ∘ k)   g = ⟹-⟨,⟩ (compose-⟹-* h k) (⟹-to-* g)
pair-⟹-* ⟨ h , k ⟩ g = ⟹-⟨,⟩ (pair-⟹-* h k) (⟹-to-* g)
pair-⟹-* (curry h) g = ⟹-⟨,⟩ (curry-⟹-* h) (⟹-to-* g)

------------------------------------------------------------------------
-- curry-⟹-* — enumerate the curry argument shapes.
-- curry-apply fires for f=apply, curry-η for f=apply ∘ ⟨h ∘ fst, snd⟩.
-- All other shapes use the structural curry-cong.
------------------------------------------------------------------------

curry-⟹-* apply                            = ⟹-curry-apply
curry-⟹-* (apply ∘ ⟨ h ∘ fst , snd ⟩)      = ⟹-curry-η (⟹-to-* h)
-- Atomic non-apply.
curry-⟹-* id                                = ⟹-curry ⟹-id
curry-⟹-* terminal                          = ⟹-curry ⟹-terminal
curry-⟹-* fst                               = ⟹-curry ⟹-fst
curry-⟹-* snd                               = ⟹-curry ⟹-snd
curry-⟹-* (curry h)                         = ⟹-curry (curry-⟹-* h)
-- Pair (curry of a pair: target product, valid).
curry-⟹-* ⟨ h , k ⟩                         = ⟹-curry (pair-⟹-* h k)
-- Compositions with non-apply head.
curry-⟹-* (id ∘ k)                          = ⟹-curry (compose-⟹-* id k)
curry-⟹-* (terminal ∘ k)                    = ⟹-curry (compose-⟹-* terminal k)
curry-⟹-* (fst ∘ k)                         = ⟹-curry (compose-⟹-* fst k)
curry-⟹-* (snd ∘ k)                         = ⟹-curry (compose-⟹-* snd k)
curry-⟹-* ((h ∘ j) ∘ k)                     = ⟹-curry (compose-⟹-* (h ∘ j) k)
curry-⟹-* (⟨ h , j ⟩ ∘ k)                   = ⟹-curry (compose-⟹-* ⟨ h , j ⟩ k)
curry-⟹-* (curry h ∘ k)                     = ⟹-curry (compose-⟹-* (curry h) k)
-- apply ∘ k where k is not the curry-η pair shape.
curry-⟹-* (apply ∘ id)                      = ⟹-curry (compose-⟹-* apply id)
curry-⟹-* (apply ∘ fst)                     = ⟹-curry (compose-⟹-* apply fst)
curry-⟹-* (apply ∘ snd)                     = ⟹-curry (compose-⟹-* apply snd)
curry-⟹-* (apply ∘ apply)                   = ⟹-curry (compose-⟹-* apply apply)
curry-⟹-* (apply ∘ (j ∘ k))                 = ⟹-curry (compose-⟹-* apply (j ∘ k))
-- apply ∘ ⟨ left , right ⟩ — sub-enumerate left.
curry-⟹-* (apply ∘ ⟨ fst , k ⟩)             = ⟹-curry (compose-⟹-* apply ⟨ fst , k ⟩)
curry-⟹-* (apply ∘ ⟨ snd , k ⟩)             = ⟹-curry (compose-⟹-* apply ⟨ snd , k ⟩)
curry-⟹-* (apply ∘ ⟨ apply , k ⟩)           = ⟹-curry (compose-⟹-* apply ⟨ apply , k ⟩)
curry-⟹-* (apply ∘ ⟨ (curry h) , k ⟩)       = ⟹-curry (compose-⟹-* apply ⟨ curry h , k ⟩)
-- apply ∘ ⟨ h ∘ ? , k ⟩ — sub-enumerate ? (8 shapes).
curry-⟹-* (apply ∘ ⟨ h ∘ id , k ⟩)          = ⟹-curry (compose-⟹-* apply ⟨ h ∘ id , k ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ terminal , k ⟩)    = ⟹-curry (compose-⟹-* apply ⟨ h ∘ terminal , k ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ snd , k ⟩)         = ⟹-curry (compose-⟹-* apply ⟨ h ∘ snd , k ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ apply , k ⟩)       = ⟹-curry (compose-⟹-* apply ⟨ h ∘ apply , k ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ (j ∘ ℓ) , k ⟩)     = ⟹-curry (compose-⟹-* apply ⟨ h ∘ (j ∘ ℓ) , k ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ ⟨ j , ℓ ⟩ , k ⟩)   = ⟹-curry (compose-⟹-* apply ⟨ h ∘ ⟨ j , ℓ ⟩ , k ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ (curry j) , k ⟩)   = ⟹-curry (compose-⟹-* apply ⟨ h ∘ (curry j) , k ⟩)
-- apply ∘ ⟨ h ∘ fst , k ⟩ with k ≠ snd — sub-enumerate k (7 shapes, snd is curry-η).
curry-⟹-* (apply ∘ ⟨ h ∘ fst , id ⟩)        = ⟹-curry (compose-⟹-* apply ⟨ h ∘ fst , id ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ fst , terminal ⟩)  = ⟹-curry (compose-⟹-* apply ⟨ h ∘ fst , terminal ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ fst , fst ⟩)       = ⟹-curry (compose-⟹-* apply ⟨ h ∘ fst , fst ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ fst , apply ⟩)     = ⟹-curry (compose-⟹-* apply ⟨ h ∘ fst , apply ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ fst , (j ∘ ℓ) ⟩)   = ⟹-curry (compose-⟹-* apply ⟨ h ∘ fst , (j ∘ ℓ) ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ fst , ⟨ j , ℓ ⟩ ⟩) = ⟹-curry (compose-⟹-* apply ⟨ h ∘ fst , ⟨ j , ℓ ⟩ ⟩)
curry-⟹-* (apply ∘ ⟨ h ∘ fst , (curry j) ⟩) = ⟹-curry (compose-⟹-* apply ⟨ h ∘ fst , (curry j) ⟩)
