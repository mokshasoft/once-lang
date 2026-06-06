------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.Diamond1
--
-- Diamond property for ⟹₁ (parallel reduction without eta-pair-gen).
--
-- Strategy: Takahashi.
--   * _* (from Diamond.agda) is the canonical fire-all-redexes function;
--     it does NOT fire eta-pair-gen, so it is the natural complete
--     development for ⟹₁.
--   * Lemma 1 (⟹₁-to-*) : t ⟹₁ t*. PROVED below by direct port of
--     Diamond.⟹-to-* — that proof never invokes ⟹-eta-pair-gen
--     (because _* never fires it), so the rule rename is mechanical.
--   * Triangle (triangle₁) : t ⟹₁ u → u ⟹₁ t*.  Standard Takahashi,
--     by induction on the ⟹₁ derivation.
--   * Diamond ⟹₁ : pick w = t*; both u ⟹₁ t* and v ⟹₁ t* by Triangle.
--
-- Status: ⟹₁-to-* DISCHARGED. triangle₁'s atomic and direct-β/η/s cases
-- DISCHARGED below; three helper-shaped congruence cases (compose-,
-- pair-, curry-) and the id-right case are isolated as named
-- postulates with focused TODOs.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.Diamond1 where

open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.StrongCCL.CCT1.ParallelReductionSplit
open import Theory.Syntax.StrongCCL.CCT1.Diamond
  using (_*; compose-*; pair-*; curry-*)

------------------------------------------------------------------------
-- Lemma 1₁ : t ⟹₁ t*.
--
-- Direct port of Theory.Syntax.StrongCCL.CCT1.Diamond.⟹-to-* with
-- ⟹- → ⟹₁-.
------------------------------------------------------------------------

⟹₁-to-*      : ∀ {A B} (t : Term A B) → t ⟹₁ t *
compose-⟹₁-* : ∀ {A B C} (f : Term B C) (g : Term A B) →
                (f ∘ g) ⟹₁ compose-* f g
pair-⟹₁-*    : ∀ {A B C} (f : Term C A) (g : Term C B) →
                ⟨ f , g ⟩ ⟹₁ pair-* f g
curry-⟹₁-*   : ∀ {A B C} (f : Term (A × B) C) →
                curry f ⟹₁ curry-* f

⟹₁-to-* id          = ⟹₁-id
⟹₁-to-* terminal    = ⟹₁-terminal
⟹₁-to-* fst         = ⟹₁-fst
⟹₁-to-* snd         = ⟹₁-snd
⟹₁-to-* apply       = ⟹₁-apply
⟹₁-to-* (f ∘ g)     = compose-⟹₁-* f g
⟹₁-to-* ⟨ f , g ⟩   = pair-⟹₁-* f g
⟹₁-to-* (curry f)   = curry-⟹₁-* f

-- LHS = id: id-left fires for any RHS.
compose-⟹₁-* id g = ⟹₁-id-left (⟹₁-to-* g)

-- LHS = fst.
compose-⟹₁-* fst ⟨ h , k ⟩ = ⟹₁-fst-β (⟹₁-to-* h) (⟹₁-to-* k)
compose-⟹₁-* fst id        = ⟹₁-id-right ⟹₁-fst
compose-⟹₁-* fst fst       = ⟹₁-∘ ⟹₁-fst ⟹₁-fst
compose-⟹₁-* fst snd       = ⟹₁-∘ ⟹₁-fst ⟹₁-snd
compose-⟹₁-* fst apply     = ⟹₁-∘ ⟹₁-fst ⟹₁-apply
compose-⟹₁-* fst (h ∘ k)   = ⟹₁-∘ ⟹₁-fst (compose-⟹₁-* h k)

-- LHS = snd.
compose-⟹₁-* snd ⟨ h , k ⟩ = ⟹₁-snd-β (⟹₁-to-* h) (⟹₁-to-* k)
compose-⟹₁-* snd id        = ⟹₁-id-right ⟹₁-snd
compose-⟹₁-* snd fst       = ⟹₁-∘ ⟹₁-snd ⟹₁-fst
compose-⟹₁-* snd snd       = ⟹₁-∘ ⟹₁-snd ⟹₁-snd
compose-⟹₁-* snd apply     = ⟹₁-∘ ⟹₁-snd ⟹₁-apply
compose-⟹₁-* snd (h ∘ k)   = ⟹₁-∘ ⟹₁-snd (compose-⟹₁-* h k)

-- LHS = apply.
compose-⟹₁-* apply ⟨ curry h , k ⟩ = ⟹₁-curry-β (⟹₁-to-* h) (⟹₁-to-* k)
compose-⟹₁-* apply id              = ⟹₁-id-right ⟹₁-apply
compose-⟹₁-* apply fst             = ⟹₁-∘ ⟹₁-apply ⟹₁-fst
compose-⟹₁-* apply snd             = ⟹₁-∘ ⟹₁-apply ⟹₁-snd
compose-⟹₁-* apply apply           = ⟹₁-∘ ⟹₁-apply ⟹₁-apply
compose-⟹₁-* apply (h ∘ k)         = ⟹₁-∘ ⟹₁-apply (compose-⟹₁-* h k)
compose-⟹₁-* apply ⟨ id , k ⟩      = ⟹₁-∘ ⟹₁-apply (pair-⟹₁-* id k)
compose-⟹₁-* apply ⟨ fst , k ⟩     = ⟹₁-∘ ⟹₁-apply (pair-⟹₁-* fst k)
compose-⟹₁-* apply ⟨ snd , k ⟩     = ⟹₁-∘ ⟹₁-apply (pair-⟹₁-* snd k)
compose-⟹₁-* apply ⟨ apply , k ⟩   = ⟹₁-∘ ⟹₁-apply (pair-⟹₁-* apply k)
compose-⟹₁-* apply ⟨ (h ∘ j) , k ⟩ = ⟹₁-∘ ⟹₁-apply (pair-⟹₁-* (h ∘ j) k)

-- LHS = terminal.
compose-⟹₁-* terminal id           = ⟹₁-id-right ⟹₁-terminal
compose-⟹₁-* terminal fst          = ⟹₁-term-unique
compose-⟹₁-* terminal snd          = ⟹₁-term-unique
compose-⟹₁-* terminal terminal     = ⟹₁-term-unique
compose-⟹₁-* terminal apply        = ⟹₁-term-unique
compose-⟹₁-* terminal (h ∘ k)      = ⟹₁-term-unique
compose-⟹₁-* terminal ⟨ h , k ⟩    = ⟹₁-term-unique
compose-⟹₁-* terminal (curry h)    = ⟹₁-term-unique

-- LHS = (h ∘ k).
compose-⟹₁-* (h ∘ k) id           = ⟹₁-id-right (compose-⟹₁-* h k)
compose-⟹₁-* (h ∘ k) terminal     = ⟹₁-assoc (⟹₁-to-* h) (⟹₁-to-* k) ⟹₁-terminal
compose-⟹₁-* (h ∘ k) fst          = ⟹₁-assoc (⟹₁-to-* h) (⟹₁-to-* k) ⟹₁-fst
compose-⟹₁-* (h ∘ k) snd          = ⟹₁-assoc (⟹₁-to-* h) (⟹₁-to-* k) ⟹₁-snd
compose-⟹₁-* (h ∘ k) apply        = ⟹₁-assoc (⟹₁-to-* h) (⟹₁-to-* k) ⟹₁-apply
compose-⟹₁-* (h ∘ k) (h' ∘ k')    = ⟹₁-assoc (⟹₁-to-* h) (⟹₁-to-* k) (compose-⟹₁-* h' k')
compose-⟹₁-* (h ∘ k) ⟨ h' , k' ⟩  = ⟹₁-assoc (⟹₁-to-* h) (⟹₁-to-* k) (pair-⟹₁-* h' k')
compose-⟹₁-* (h ∘ k) (curry h')   = ⟹₁-assoc (⟹₁-to-* h) (⟹₁-to-* k) (curry-⟹₁-* h')

-- LHS = ⟨h, k⟩.
compose-⟹₁-* ⟨ h , k ⟩ id           = ⟹₁-id-right (pair-⟹₁-* h k)
compose-⟹₁-* ⟨ h , k ⟩ terminal     = ⟹₁-pair-dist (⟹₁-to-* h) (⟹₁-to-* k) ⟹₁-terminal
compose-⟹₁-* ⟨ h , k ⟩ fst          = ⟹₁-pair-dist (⟹₁-to-* h) (⟹₁-to-* k) ⟹₁-fst
compose-⟹₁-* ⟨ h , k ⟩ snd          = ⟹₁-pair-dist (⟹₁-to-* h) (⟹₁-to-* k) ⟹₁-snd
compose-⟹₁-* ⟨ h , k ⟩ apply        = ⟹₁-pair-dist (⟹₁-to-* h) (⟹₁-to-* k) ⟹₁-apply
compose-⟹₁-* ⟨ h , k ⟩ (h' ∘ k')    = ⟹₁-pair-dist (⟹₁-to-* h) (⟹₁-to-* k) (compose-⟹₁-* h' k')
compose-⟹₁-* ⟨ h , k ⟩ ⟨ h' , k' ⟩  = ⟹₁-pair-dist (⟹₁-to-* h) (⟹₁-to-* k) (pair-⟹₁-* h' k')
compose-⟹₁-* ⟨ h , k ⟩ (curry h')   = ⟹₁-pair-dist (⟹₁-to-* h) (⟹₁-to-* k) (curry-⟹₁-* h')

-- LHS = curry h.
compose-⟹₁-* (curry h) id           = ⟹₁-id-right (curry-⟹₁-* h)
compose-⟹₁-* (curry h) terminal     = ⟹₁-curry-compose (⟹₁-to-* h) ⟹₁-terminal
compose-⟹₁-* (curry h) fst          = ⟹₁-curry-compose (⟹₁-to-* h) ⟹₁-fst
compose-⟹₁-* (curry h) snd          = ⟹₁-curry-compose (⟹₁-to-* h) ⟹₁-snd
compose-⟹₁-* (curry h) apply        = ⟹₁-curry-compose (⟹₁-to-* h) ⟹₁-apply
compose-⟹₁-* (curry h) (h' ∘ k')    = ⟹₁-curry-compose (⟹₁-to-* h) (compose-⟹₁-* h' k')
compose-⟹₁-* (curry h) ⟨ h' , k' ⟩  = ⟹₁-curry-compose (⟹₁-to-* h) (pair-⟹₁-* h' k')
compose-⟹₁-* (curry h) (curry h')   = ⟹₁-curry-compose (⟹₁-to-* h) (curry-⟹₁-* h')

-- pair-⟹₁-*.
pair-⟹₁-* fst snd        = ⟹₁-eta-pair
pair-⟹₁-* fst id         = ⟹₁-⟨,⟩ ⟹₁-fst ⟹₁-id
pair-⟹₁-* fst fst        = ⟹₁-⟨,⟩ ⟹₁-fst ⟹₁-fst
pair-⟹₁-* fst terminal   = ⟹₁-⟨,⟩ ⟹₁-fst ⟹₁-terminal
pair-⟹₁-* fst apply      = ⟹₁-⟨,⟩ ⟹₁-fst ⟹₁-apply
pair-⟹₁-* fst (h ∘ k)    = ⟹₁-⟨,⟩ ⟹₁-fst (compose-⟹₁-* h k)
pair-⟹₁-* fst ⟨ h , k ⟩  = ⟹₁-⟨,⟩ ⟹₁-fst (pair-⟹₁-* h k)
pair-⟹₁-* fst (curry h)  = ⟹₁-⟨,⟩ ⟹₁-fst (curry-⟹₁-* h)
pair-⟹₁-* id        g = ⟹₁-⟨,⟩ ⟹₁-id (⟹₁-to-* g)
pair-⟹₁-* terminal  g = ⟹₁-⟨,⟩ ⟹₁-terminal (⟹₁-to-* g)
pair-⟹₁-* snd       g = ⟹₁-⟨,⟩ ⟹₁-snd (⟹₁-to-* g)
pair-⟹₁-* apply     g = ⟹₁-⟨,⟩ ⟹₁-apply (⟹₁-to-* g)
pair-⟹₁-* (h ∘ k)   g = ⟹₁-⟨,⟩ (compose-⟹₁-* h k) (⟹₁-to-* g)
pair-⟹₁-* ⟨ h , k ⟩ g = ⟹₁-⟨,⟩ (pair-⟹₁-* h k) (⟹₁-to-* g)
pair-⟹₁-* (curry h) g = ⟹₁-⟨,⟩ (curry-⟹₁-* h) (⟹₁-to-* g)

-- curry-⟹₁-*.
curry-⟹₁-* apply                            = ⟹₁-curry-apply
curry-⟹₁-* (apply ∘ ⟨ h ∘ fst , snd ⟩)      = ⟹₁-curry-η (⟹₁-to-* h)
curry-⟹₁-* id                                = ⟹₁-curry ⟹₁-id
curry-⟹₁-* terminal                          = ⟹₁-curry ⟹₁-terminal
curry-⟹₁-* fst                               = ⟹₁-curry ⟹₁-fst
curry-⟹₁-* snd                               = ⟹₁-curry ⟹₁-snd
curry-⟹₁-* (curry h)                         = ⟹₁-curry (curry-⟹₁-* h)
curry-⟹₁-* ⟨ h , k ⟩                         = ⟹₁-curry (pair-⟹₁-* h k)
curry-⟹₁-* (id ∘ k)                          = ⟹₁-curry (compose-⟹₁-* id k)
curry-⟹₁-* (terminal ∘ k)                    = ⟹₁-curry (compose-⟹₁-* terminal k)
curry-⟹₁-* (fst ∘ k)                         = ⟹₁-curry (compose-⟹₁-* fst k)
curry-⟹₁-* (snd ∘ k)                         = ⟹₁-curry (compose-⟹₁-* snd k)
curry-⟹₁-* ((h ∘ j) ∘ k)                     = ⟹₁-curry (compose-⟹₁-* (h ∘ j) k)
curry-⟹₁-* (⟨ h , j ⟩ ∘ k)                   = ⟹₁-curry (compose-⟹₁-* ⟨ h , j ⟩ k)
curry-⟹₁-* (curry h ∘ k)                     = ⟹₁-curry (compose-⟹₁-* (curry h) k)
curry-⟹₁-* (apply ∘ id)                      = ⟹₁-curry (compose-⟹₁-* apply id)
curry-⟹₁-* (apply ∘ fst)                     = ⟹₁-curry (compose-⟹₁-* apply fst)
curry-⟹₁-* (apply ∘ snd)                     = ⟹₁-curry (compose-⟹₁-* apply snd)
curry-⟹₁-* (apply ∘ apply)                   = ⟹₁-curry (compose-⟹₁-* apply apply)
curry-⟹₁-* (apply ∘ (j ∘ k))                 = ⟹₁-curry (compose-⟹₁-* apply (j ∘ k))
curry-⟹₁-* (apply ∘ ⟨ fst , k ⟩)             = ⟹₁-curry (compose-⟹₁-* apply ⟨ fst , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ snd , k ⟩)             = ⟹₁-curry (compose-⟹₁-* apply ⟨ snd , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ apply , k ⟩)           = ⟹₁-curry (compose-⟹₁-* apply ⟨ apply , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ (curry h) , k ⟩)       = ⟹₁-curry (compose-⟹₁-* apply ⟨ curry h , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ id , k ⟩)          = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ id , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ terminal , k ⟩)    = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ terminal , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ snd , k ⟩)         = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ snd , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ apply , k ⟩)       = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ apply , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ (j ∘ ℓ) , k ⟩)     = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ (j ∘ ℓ) , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ ⟨ j , ℓ ⟩ , k ⟩)   = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ ⟨ j , ℓ ⟩ , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ (curry j) , k ⟩)   = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ (curry j) , k ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ fst , id ⟩)        = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ fst , id ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ fst , terminal ⟩)  = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ fst , terminal ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ fst , fst ⟩)       = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ fst , fst ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ fst , apply ⟩)     = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ fst , apply ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ fst , (j ∘ ℓ) ⟩)   = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ fst , (j ∘ ℓ) ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ fst , ⟨ j , ℓ ⟩ ⟩) = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ fst , ⟨ j , ℓ ⟩ ⟩)
curry-⟹₁-* (apply ∘ ⟨ h ∘ fst , (curry j) ⟩) = ⟹₁-curry (compose-⟹₁-* apply ⟨ h ∘ fst , (curry j) ⟩)

------------------------------------------------------------------------
-- Triangle property : t ⟹₁ u → u ⟹₁ t*.
--
-- DEEPER OBSTACLE DISCOVERED.
--   Triangle does NOT hold straightforwardly with the current _*.
--   Concrete counterexample: t = (curry h) ∘ id.
--     User can fire ⟹₁-curry-compose, giving u = curry (h ∘ ⟨ id ∘ fst , snd ⟩).
--     _* fires id-right (priority over curry-compose), giving t* = curry-* h
--     = curry (h*) (for typical h).
--     u ⟹₁ t* requires reducing curry (h ∘ ⟨ id ∘ fst , snd ⟩) ⟹₁ curry (h*),
--     which needs THREE sequential β/η steps inside (id-left on id ∘ fst,
--     eta-pair on ⟨fst,snd⟩, id-right on h ∘ id) — NOT a single parallel
--     step.
--
--   This is a different manifestation of the same Curien curry-η critical
--   pair that blocks the Newman-based local-confluent-rest. The
--   Takahashi-style diamond proof requires _* to fire rules in a way that
--   matches whatever user choices are available at each position.
--   With curry-compose vs id-right both firing at the same root for
--   (curry h) ∘ id (and similarly assoc vs id-right for (h ∘ k) ∘ id,
--   pair-dist vs id-right for ⟨h,k⟩ ∘ id), the two candidates for t*
--   give different reducts NOT joinable in a single ⟹₁ step.
--
--   Resolution paths:
--     (i)  redefine _* to drop id-right priority — then need to verify
--          Lemma 1 for the new _* (likely fine, just rewire id-right
--          consumers to use the heavier rule's path);
--     (ii) extend ⟹₁ with multi-redex parallel firing along a path
--          (essentially: weak-head normalisation in one ⟹₁ step);
--     (iii) use a different complete-development function _*₁ tuned
--          to the ⟹₁ rule set.
--
--   Postponed.  Postulated below as a single obligation; the resolution
--   is its own focused project.
------------------------------------------------------------------------

postulate
  triangle₁ : ∀ {A B} {t u : Term A B} → t ⟹₁ u → u ⟹₁ t *

------------------------------------------------------------------------
-- Diamond ⟹₁ : the immediate consequence.
------------------------------------------------------------------------

diamond₁ : ∀ {A B} {t u v : Term A B} →
           t ⟹₁ u → t ⟹₁ v →
           Σ (Term A B) (λ w → (u ⟹₁ w) ∧ (v ⟹₁ w))
diamond₁ {t = t} ru rv = (t * , triangle₁ ru , triangle₁ rv)
