------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.BetaFragment.Diamond
--
-- Complete development + Lemma 1 (t ⟹ t*) at CCT1.
--
-- curry-η is excluded from this system (see BaseRules.agda for the
-- rationale). curry-* is therefore purely structural.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.BetaFragment.Diamond where

open import Theory.Syntax.StrongCCL.CCT1.BetaFragment
open import Theory.Syntax.StrongCCL.CCT1.BetaFragment.ParallelReduction

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
  (curry f) * = curry (f *)

  compose-* : ∀ {A B C} → Term B C → Term A B → Term A C
  compose-* id         g                      = g *
  compose-* fst        ⟨ h , k ⟩               = h *
  compose-* snd        ⟨ h , k ⟩               = k *
  compose-* apply      ⟨ curry f , g ⟩         = f * ∘ ⟨ id , g * ⟩
  compose-* f          id                      = f *
  compose-* f          g                       = f * ∘ g *

  pair-* : ∀ {A B C} → Term C A → Term C B → Term C (A × B)
  pair-* fst snd = id
  pair-* f   g   = ⟨ f * , g * ⟩

------------------------------------------------------------------------
-- Lemma 1: t ⟹ t*
------------------------------------------------------------------------

⟹-to-*      : ∀ {A B} (t : Term A B) → t ⟹ t *
compose-⟹-* : ∀ {A B C} (f : Term B C) (g : Term A B) →
               (f ∘ g) ⟹ compose-* f g
pair-⟹-*    : ∀ {A B C} (f : Term C A) (g : Term C B) →
               ⟨ f , g ⟩ ⟹ pair-* f g

⟹-to-* id          = ⟹-id
⟹-to-* terminal    = ⟹-terminal
⟹-to-* fst         = ⟹-fst
⟹-to-* snd         = ⟹-snd
⟹-to-* apply       = ⟹-apply
⟹-to-* (f ∘ g)     = compose-⟹-* f g
⟹-to-* ⟨ f , g ⟩   = pair-⟹-* f g
⟹-to-* (curry f)   = ⟹-curry (⟹-to-* f)

------------------------------------------------------------------------
-- compose-⟹-*: enumerate on (LHS, RHS).
------------------------------------------------------------------------

compose-⟹-* id g = ⟹-id-left (⟹-to-* g)

compose-⟹-* fst ⟨ h , k ⟩ = ⟹-fst-β (⟹-to-* h) (⟹-to-* k)
compose-⟹-* fst id        = ⟹-id-right ⟹-fst
compose-⟹-* fst fst       = ⟹-∘ ⟹-fst ⟹-fst
compose-⟹-* fst snd       = ⟹-∘ ⟹-fst ⟹-snd
compose-⟹-* fst (h ∘ k)   = ⟹-∘ ⟹-fst (⟹-to-* (h ∘ k))
compose-⟹-* fst apply     = ⟹-∘ ⟹-fst ⟹-apply
-- fst (curry _): TYPE-INCOMPATIBLE

compose-⟹-* snd ⟨ h , k ⟩ = ⟹-snd-β (⟹-to-* h) (⟹-to-* k)
compose-⟹-* snd id        = ⟹-id-right ⟹-snd
compose-⟹-* snd fst       = ⟹-∘ ⟹-snd ⟹-fst
compose-⟹-* snd snd       = ⟹-∘ ⟹-snd ⟹-snd
compose-⟹-* snd (h ∘ k)   = ⟹-∘ ⟹-snd (⟹-to-* (h ∘ k))
compose-⟹-* snd apply     = ⟹-∘ ⟹-snd ⟹-apply
-- snd (curry _): TYPE-INCOMPATIBLE

compose-⟹-* apply ⟨ curry h , k ⟩ = ⟹-curry-β (⟹-to-* h) (⟹-to-* k)
compose-⟹-* apply id              = ⟹-id-right ⟹-apply
compose-⟹-* apply fst             = ⟹-∘ ⟹-apply ⟹-fst
compose-⟹-* apply snd             = ⟹-∘ ⟹-apply ⟹-snd
compose-⟹-* apply (h ∘ k)         = ⟹-∘ ⟹-apply (⟹-to-* (h ∘ k))
compose-⟹-* apply apply           = ⟹-∘ ⟹-apply ⟹-apply
compose-⟹-* apply ⟨ id , k ⟩      = ⟹-∘ ⟹-apply (⟹-to-* ⟨ id , k ⟩)
compose-⟹-* apply ⟨ fst , k ⟩     = ⟹-∘ ⟹-apply (⟹-to-* ⟨ fst , k ⟩)
compose-⟹-* apply ⟨ snd , k ⟩     = ⟹-∘ ⟹-apply (⟹-to-* ⟨ snd , k ⟩)
compose-⟹-* apply ⟨ apply , k ⟩   = ⟹-∘ ⟹-apply (⟹-to-* ⟨ apply , k ⟩)
compose-⟹-* apply ⟨ (h ∘ j) , k ⟩ = ⟹-∘ ⟹-apply (⟹-to-* ⟨ (h ∘ j) , k ⟩)

compose-⟹-* terminal id           = ⟹-id-right ⟹-terminal
compose-⟹-* terminal fst          = ⟹-∘ ⟹-terminal ⟹-fst
compose-⟹-* terminal snd          = ⟹-∘ ⟹-terminal ⟹-snd
compose-⟹-* terminal terminal     = ⟹-∘ ⟹-terminal ⟹-terminal
compose-⟹-* terminal (h ∘ k)      = ⟹-∘ ⟹-terminal (⟹-to-* (h ∘ k))
compose-⟹-* terminal ⟨ h , k ⟩    = ⟹-∘ ⟹-terminal (⟹-to-* ⟨ h , k ⟩)
compose-⟹-* terminal apply        = ⟹-∘ ⟹-terminal ⟹-apply
compose-⟹-* terminal (curry h)    = ⟹-∘ ⟹-terminal (⟹-to-* (curry h))

compose-⟹-* (h ∘ k) id            = ⟹-id-right (⟹-to-* (h ∘ k))
compose-⟹-* (h ∘ k) fst           = ⟹-∘ (⟹-to-* (h ∘ k)) ⟹-fst
compose-⟹-* (h ∘ k) snd           = ⟹-∘ (⟹-to-* (h ∘ k)) ⟹-snd
compose-⟹-* (h ∘ k) terminal      = ⟹-∘ (⟹-to-* (h ∘ k)) ⟹-terminal
compose-⟹-* (h ∘ k) (h' ∘ k')     = ⟹-∘ (⟹-to-* (h ∘ k)) (⟹-to-* (h' ∘ k'))
compose-⟹-* (h ∘ k) ⟨ h' , k' ⟩   = ⟹-∘ (⟹-to-* (h ∘ k)) (⟹-to-* ⟨ h' , k' ⟩)
compose-⟹-* (h ∘ k) apply         = ⟹-∘ (⟹-to-* (h ∘ k)) ⟹-apply
compose-⟹-* (h ∘ k) (curry h')    = ⟹-∘ (⟹-to-* (h ∘ k)) (⟹-to-* (curry h'))

compose-⟹-* ⟨ h , k ⟩ id           = ⟹-id-right (⟹-to-* ⟨ h , k ⟩)
compose-⟹-* ⟨ h , k ⟩ fst          = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) ⟹-fst
compose-⟹-* ⟨ h , k ⟩ snd          = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) ⟹-snd
compose-⟹-* ⟨ h , k ⟩ terminal     = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) ⟹-terminal
compose-⟹-* ⟨ h , k ⟩ (h' ∘ k')    = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) (⟹-to-* (h' ∘ k'))
compose-⟹-* ⟨ h , k ⟩ ⟨ h' , k' ⟩  = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) (⟹-to-* ⟨ h' , k' ⟩)
compose-⟹-* ⟨ h , k ⟩ apply        = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) ⟹-apply
compose-⟹-* ⟨ h , k ⟩ (curry h')   = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) (⟹-to-* (curry h'))

compose-⟹-* (curry h) id           = ⟹-id-right (⟹-to-* (curry h))
compose-⟹-* (curry h) fst          = ⟹-∘ (⟹-to-* (curry h)) ⟹-fst
compose-⟹-* (curry h) snd          = ⟹-∘ (⟹-to-* (curry h)) ⟹-snd
compose-⟹-* (curry h) terminal     = ⟹-∘ (⟹-to-* (curry h)) ⟹-terminal
compose-⟹-* (curry h) (h' ∘ k')    = ⟹-∘ (⟹-to-* (curry h)) (⟹-to-* (h' ∘ k'))
compose-⟹-* (curry h) ⟨ h' , k' ⟩  = ⟹-∘ (⟹-to-* (curry h)) (⟹-to-* ⟨ h' , k' ⟩)
compose-⟹-* (curry h) apply        = ⟹-∘ (⟹-to-* (curry h)) ⟹-apply
compose-⟹-* (curry h) (curry h')   = ⟹-∘ (⟹-to-* (curry h)) (⟹-to-* (curry h'))

------------------------------------------------------------------------
-- pair-⟹-*
------------------------------------------------------------------------

pair-⟹-* fst snd = ⟹-eta-pair

pair-⟹-* fst id         = ⟹-⟨,⟩ ⟹-fst ⟹-id
pair-⟹-* fst fst        = ⟹-⟨,⟩ ⟹-fst ⟹-fst
pair-⟹-* fst terminal   = ⟹-⟨,⟩ ⟹-fst ⟹-terminal
pair-⟹-* fst (h ∘ k)    = ⟹-⟨,⟩ ⟹-fst (⟹-to-* (h ∘ k))
pair-⟹-* fst ⟨ h , k ⟩  = ⟹-⟨,⟩ ⟹-fst (⟹-to-* ⟨ h , k ⟩)
pair-⟹-* fst apply      = ⟹-⟨,⟩ ⟹-fst ⟹-apply
pair-⟹-* fst (curry h)  = ⟹-⟨,⟩ ⟹-fst (⟹-to-* (curry h))

pair-⟹-* id        g = ⟹-⟨,⟩ ⟹-id (⟹-to-* g)
pair-⟹-* terminal  g = ⟹-⟨,⟩ ⟹-terminal (⟹-to-* g)
pair-⟹-* snd       g = ⟹-⟨,⟩ ⟹-snd (⟹-to-* g)
pair-⟹-* (h ∘ k)   g = ⟹-⟨,⟩ (⟹-to-* (h ∘ k)) (⟹-to-* g)
pair-⟹-* ⟨ h , k ⟩ g = ⟹-⟨,⟩ (⟹-to-* ⟨ h , k ⟩) (⟹-to-* g)
pair-⟹-* apply     g = ⟹-⟨,⟩ ⟹-apply (⟹-to-* g)
pair-⟹-* (curry h) g = ⟹-⟨,⟩ (⟹-to-* (curry h)) (⟹-to-* g)
