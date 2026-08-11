------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCTB.BetaFragment.Diamond
--
-- Takahashi-style diamond proof for CCTB parallel reduction.
--
-- Lemma 1 (this file, the hard part): t ⟹ t* for all t, where t* is
-- the complete development of t.
--
-- Triangle (t ⟹ u → u ⟹ t*) and diamond follow from Lemma 1 plus
-- further case analysis on u; those are deferred to a follow-up file
-- once Lemma 1 is stabilized.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCTB.BetaFragment.Diamond where

open import Theory.Syntax.StrongCCL.CCTB.BetaFragment
open import Theory.Syntax.StrongCCL.CCTB.BetaFragment.ParallelReduction

------------------------------------------------------------------------
-- Complete development _*
------------------------------------------------------------------------

mutual
  _* : ∀ {A B} → Term A B → Term A B
  id *        = id
  terminal *  = terminal
  fst *       = fst
  snd *       = snd
  (f ∘ g) *   = compose-* f g
  ⟨ f , g ⟩ * = pair-* f g

  compose-* : ∀ {A B C} → Term B C → Term A B → Term A C
  compose-* id         g          = g *
  compose-* fst        ⟨ h , k ⟩  = h *
  compose-* snd        ⟨ h , k ⟩  = k *
  compose-* f          id         = f *
  compose-* f          g          = f * ∘ g *

  pair-* : ∀ {A B C} → Term C A → Term C B → Term C (A × B)
  pair-* fst snd = id
  pair-* f   g   = ⟨ f * , g * ⟩

------------------------------------------------------------------------
-- Lemma 1: every term parallel-reduces to its complete development.
--
-- Enumerated explicitly (no abstract pattern variables) because Agda
-- won't reduce compose-* / pair-* when given abstract arguments due
-- to the overlapping clause structure.
------------------------------------------------------------------------

⟹-to-* : ∀ {A B} (t : Term A B) → t ⟹ t *

-- compose cases, enumerated on (LHS, RHS) shape
compose-⟹-* : ∀ {A B C} (f : Term B C) (g : Term A B) →
               (f ∘ g) ⟹ compose-* f g

-- pair cases, enumerated similarly
pair-⟹-* : ∀ {A B C} (f : Term C A) (g : Term C B) →
            ⟨ f , g ⟩ ⟹ pair-* f g

-- Top-level ⟹-to-*
⟹-to-* id          = ⟹-id
⟹-to-* terminal    = ⟹-terminal
⟹-to-* fst         = ⟹-fst
⟹-to-* snd         = ⟹-snd
⟹-to-* (f ∘ g)     = compose-⟹-* f g
⟹-to-* ⟨ f , g ⟩   = pair-⟹-* f g

-- compose-⟹-*: full enumeration over LHS × RHS shapes.

-- LHS = id (any RHS)
compose-⟹-* id g = ⟹-id-left (⟹-to-* g)

-- LHS = fst
compose-⟹-* fst id           = ⟹-id-right ⟹-fst
compose-⟹-* fst fst          = ⟹-∘ ⟹-fst ⟹-fst
compose-⟹-* fst snd          = ⟹-∘ ⟹-fst ⟹-snd
compose-⟹-* fst (h ∘ k)      = ⟹-∘ ⟹-fst (⟹-to-* (h ∘ k))
compose-⟹-* fst ⟨ h , k ⟩    = ⟹-fst-β (⟹-to-* h) (⟹-to-* k)

-- LHS = snd
compose-⟹-* snd id           = ⟹-id-right ⟹-snd
compose-⟹-* snd fst          = ⟹-∘ ⟹-snd ⟹-fst
compose-⟹-* snd snd          = ⟹-∘ ⟹-snd ⟹-snd
compose-⟹-* snd (h ∘ k)      = ⟹-∘ ⟹-snd (⟹-to-* (h ∘ k))
compose-⟹-* snd ⟨ h , k ⟩    = ⟹-snd-β (⟹-to-* h) (⟹-to-* k)

-- LHS = terminal
compose-⟹-* terminal id           = ⟹-id-right ⟹-terminal
compose-⟹-* terminal fst          = ⟹-∘ ⟹-terminal ⟹-fst
compose-⟹-* terminal snd          = ⟹-∘ ⟹-terminal ⟹-snd
compose-⟹-* terminal terminal     = ⟹-∘ ⟹-terminal ⟹-terminal
compose-⟹-* terminal (h ∘ k)      = ⟹-∘ ⟹-terminal (⟹-to-* (h ∘ k))
compose-⟹-* terminal ⟨ h , k ⟩    = ⟹-∘ ⟹-terminal (⟹-to-* ⟨ h , k ⟩)

-- LHS = (_ ∘ _)
compose-⟹-* (h ∘ k) id           = ⟹-id-right (⟹-to-* (h ∘ k))
compose-⟹-* (h ∘ k) fst          = ⟹-∘ (⟹-to-* (h ∘ k)) ⟹-fst
compose-⟹-* (h ∘ k) snd          = ⟹-∘ (⟹-to-* (h ∘ k)) ⟹-snd
compose-⟹-* (h ∘ k) terminal     = ⟹-∘ (⟹-to-* (h ∘ k)) ⟹-terminal
compose-⟹-* (h ∘ k) (h' ∘ k')    = ⟹-∘ (⟹-to-* (h ∘ k)) (⟹-to-* (h' ∘ k'))
compose-⟹-* (h ∘ k) ⟨ h' , k' ⟩  = ⟹-∘ (⟹-to-* (h ∘ k)) (⟹-to-* ⟨ h' , k' ⟩)

-- LHS = ⟨ _ , _ ⟩
compose-⟹-* ⟨ h , k ⟩ id           = ⟹-id-right (⟹-to-* ⟨ h , k ⟩)
compose-⟹-* ⟨ h , k ⟩ fst          = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) ⟹-fst
compose-⟹-* ⟨ h , k ⟩ snd          = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) ⟹-snd
compose-⟹-* ⟨ h , k ⟩ terminal     = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) ⟹-terminal
compose-⟹-* ⟨ h , k ⟩ (h' ∘ k')    = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) (⟹-to-* (h' ∘ k'))
compose-⟹-* ⟨ h , k ⟩ ⟨ h' , k' ⟩  = ⟹-∘ (⟹-to-* ⟨ h , k ⟩) (⟹-to-* ⟨ h' , k' ⟩)

-- pair-⟹-*: enumerate over (LHS, RHS) shapes too.

-- The one special case: eta-pair.
pair-⟹-* fst snd = ⟹-eta-pair

-- All other cases default to structural ⟹-⟨,⟩.
-- LHS = id
pair-⟹-* id g = ⟹-⟨,⟩ ⟹-id (⟹-to-* g)

-- LHS = terminal
pair-⟹-* terminal g = ⟹-⟨,⟩ ⟹-terminal (⟹-to-* g)

-- LHS = (_ ∘ _)
pair-⟹-* (h ∘ k) g = ⟹-⟨,⟩ (⟹-to-* (h ∘ k)) (⟹-to-* g)

-- LHS = ⟨ _, _ ⟩
pair-⟹-* ⟨ h , k ⟩ g = ⟹-⟨,⟩ (⟹-to-* ⟨ h , k ⟩) (⟹-to-* g)

-- LHS = fst (RHS ≠ snd: not eta)
pair-⟹-* fst id           = ⟹-⟨,⟩ ⟹-fst ⟹-id
pair-⟹-* fst fst          = ⟹-⟨,⟩ ⟹-fst ⟹-fst
pair-⟹-* fst terminal     = ⟹-⟨,⟩ ⟹-fst ⟹-terminal
pair-⟹-* fst (h ∘ k)      = ⟹-⟨,⟩ ⟹-fst (⟹-to-* (h ∘ k))
pair-⟹-* fst ⟨ h , k ⟩    = ⟹-⟨,⟩ ⟹-fst (⟹-to-* ⟨ h , k ⟩)

-- LHS = snd
pair-⟹-* snd g = ⟹-⟨,⟩ ⟹-snd (⟹-to-* g)
