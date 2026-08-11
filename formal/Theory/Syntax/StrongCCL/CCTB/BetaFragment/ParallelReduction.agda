------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCTB.BetaFragment.ParallelReduction
--
-- Parallel reduction at CCTB, and its equivalence with ⟶* via two
-- bridges:
--   ⟶-to-⟹  : single reduction step embeds as a parallel step
--   ⟹-to-⟶* : a parallel step expands to a finite reduction sequence
--
-- All proofs by structural induction.
--
-- This module is the foundation for the diamond-property proof
-- (Theory.Syntax.CCTB.Diamond) which in turn gives CCTB confluence.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCTB.BetaFragment.ParallelReduction where

open import Theory.Syntax.StrongCCL.CCTB.BetaFragment

------------------------------------------------------------------------
-- Parallel reduction
--
-- Fires all in-situ redexes at once. Structural under composition and
-- pairing; β/η-reduces at the top when a redex pattern appears.
------------------------------------------------------------------------

data _⟹_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Atomic reflexivity (generators that have no subterms)
  ⟹-id       : ∀ {A}     → id {A} ⟹ id
  ⟹-terminal : ∀ {A}     → terminal {A} ⟹ terminal
  ⟹-fst      : ∀ {A B}   → fst {A} {B} ⟹ fst
  ⟹-snd      : ∀ {A B}   → snd {A} {B} ⟹ snd

  -- Structural (no redex fires)
  ⟹-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
        f ⟹ f' → g ⟹ g' → (f ∘ g) ⟹ (f' ∘ g')
  ⟹-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟹ f' → g ⟹ g' → ⟨ f , g ⟩ ⟹ ⟨ f' , g' ⟩

  -- β-reductions (fire at top + reduce subterms in parallel)
  ⟹-fst-β : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            f ⟹ f' → g ⟹ g' → (fst ∘ ⟨ f , g ⟩) ⟹ f'
  ⟹-snd-β : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            f ⟹ f' → g ⟹ g' → (snd ∘ ⟨ f , g ⟩) ⟹ g'

  -- η-reduction (no subterms to reduce)
  ⟹-eta-pair : ∀ {A B} → ⟨ fst {A} {B} , snd ⟩ ⟹ id

  -- Identity laws (fire at top + reduce the surviving subterm)
  ⟹-id-left  : ∀ {A B} {f f' : Term A B} →
               f ⟹ f' → (id ∘ f) ⟹ f'
  ⟹-id-right : ∀ {A B} {f f' : Term A B} →
               f ⟹ f' → (f ∘ id) ⟹ f'

infix 4 _⟹_

------------------------------------------------------------------------
-- Reflexivity: every term parallel-reduces to itself.
------------------------------------------------------------------------

⟹-refl : ∀ {A B} (t : Term A B) → t ⟹ t
⟹-refl id          = ⟹-id
⟹-refl terminal    = ⟹-terminal
⟹-refl fst         = ⟹-fst
⟹-refl snd         = ⟹-snd
⟹-refl (f ∘ g)     = ⟹-∘ (⟹-refl f) (⟹-refl g)
⟹-refl ⟨ f , g ⟩   = ⟹-⟨,⟩ (⟹-refl f) (⟹-refl g)

------------------------------------------------------------------------
-- Bridge 1: single reduction step embeds as a parallel step.
--
-- For each base β/η rule we use the corresponding parallel rule.
-- For congruence rules we use structural parallel + reflexivity.
------------------------------------------------------------------------

⟶-to-⟹ : ∀ {A B} {f g : Term A B} → f ⟶ g → f ⟹ g
⟶-to-⟹ (base fst-pair)    = ⟹-fst-β (⟹-refl _) (⟹-refl _)
⟶-to-⟹ (base snd-pair)    = ⟹-snd-β (⟹-refl _) (⟹-refl _)
⟶-to-⟹ (base eta-pair)    = ⟹-eta-pair
⟶-to-⟹ (base id-left)     = ⟹-id-left (⟹-refl _)
⟶-to-⟹ (base id-right)    = ⟹-id-right (⟹-refl _)
⟶-to-⟹ (∘-congˡ r)        = ⟹-∘ (⟶-to-⟹ r) (⟹-refl _)
⟶-to-⟹ (∘-congʳ r)        = ⟹-∘ (⟹-refl _) (⟶-to-⟹ r)
⟶-to-⟹ (⟨,⟩-congˡ r)      = ⟹-⟨,⟩ (⟶-to-⟹ r) (⟹-refl _)
⟶-to-⟹ (⟨,⟩-congʳ r)      = ⟹-⟨,⟩ (⟹-refl _) (⟶-to-⟹ r)

------------------------------------------------------------------------
-- Bridge 2: a parallel step expands to a reduction sequence.
--
-- The structural cases (⟹-∘, ⟹-⟨,⟩) require lifting reductions into
-- larger contexts, so we first build the congruence lemmas for ⟶*.
------------------------------------------------------------------------

⟶*-trans : ∀ {A B} {t u v : Term A B} → t ⟶* u → u ⟶* v → t ⟶* v
⟶*-trans done         yz = yz
⟶*-trans (r ∷ xy)     yz = r ∷ ⟶*-trans xy yz

⟶*-∘ˡ : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
        f ⟶* f' → (f ∘ g) ⟶* (f' ∘ g)
⟶*-∘ˡ done       = done
⟶*-∘ˡ (r ∷ rs)   = ∘-congˡ r ∷ ⟶*-∘ˡ rs

⟶*-∘ʳ : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
        g ⟶* g' → (f ∘ g) ⟶* (f ∘ g')
⟶*-∘ʳ done       = done
⟶*-∘ʳ (r ∷ rs)   = ∘-congʳ r ∷ ⟶*-∘ʳ rs

⟶*-⟨,⟩ˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
          f ⟶* f' → ⟨ f , g ⟩ ⟶* ⟨ f' , g ⟩
⟶*-⟨,⟩ˡ done     = done
⟶*-⟨,⟩ˡ (r ∷ rs) = ⟨,⟩-congˡ r ∷ ⟶*-⟨,⟩ˡ rs

⟶*-⟨,⟩ʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
          g ⟶* g' → ⟨ f , g ⟩ ⟶* ⟨ f , g' ⟩
⟶*-⟨,⟩ʳ done     = done
⟶*-⟨,⟩ʳ (r ∷ rs) = ⟨,⟩-congʳ r ∷ ⟶*-⟨,⟩ʳ rs

-- Composition inside reductions (both arguments reduce)
⟶*-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
       f ⟶* f' → g ⟶* g' → (f ∘ g) ⟶* (f' ∘ g')
⟶*-∘ ff gg = ⟶*-trans (⟶*-∘ˡ ff) (⟶*-∘ʳ gg)

⟶*-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
         f ⟶* f' → g ⟶* g' → ⟨ f , g ⟩ ⟶* ⟨ f' , g' ⟩
⟶*-⟨,⟩ ff gg = ⟶*-trans (⟶*-⟨,⟩ˡ ff) (⟶*-⟨,⟩ʳ gg)

-- Single step as a reduction sequence
⟶-to-⟶* : ∀ {A B} {f g : Term A B} → f ⟶ g → f ⟶* g
⟶-to-⟶* r = r ∷ done

------------------------------------------------------------------------
-- Now the main bridge: ⟹ expands to ⟶*
------------------------------------------------------------------------

⟹-to-⟶* : ∀ {A B} {f g : Term A B} → f ⟹ g → f ⟶* g
⟹-to-⟶* ⟹-id              = done
⟹-to-⟶* ⟹-terminal        = done
⟹-to-⟶* ⟹-fst             = done
⟹-to-⟶* ⟹-snd             = done
⟹-to-⟶* (⟹-∘ rf rg)       = ⟶*-∘ (⟹-to-⟶* rf) (⟹-to-⟶* rg)
⟹-to-⟶* (⟹-⟨,⟩ rf rg)     = ⟶*-⟨,⟩ (⟹-to-⟶* rf) (⟹-to-⟶* rg)
⟹-to-⟶* (⟹-fst-β rf rg)   =
  -- Reduce f ∘ ⟨ f , g ⟩ to fst ∘ ⟨ f' , g' ⟩ structurally, then β.
  ⟶*-trans (⟶*-∘ʳ (⟶*-⟨,⟩ (⟹-to-⟶* rf) (⟹-to-⟶* rg)))
           (⟶-to-⟶* (base fst-pair))
⟹-to-⟶* (⟹-snd-β rf rg)   =
  ⟶*-trans (⟶*-∘ʳ (⟶*-⟨,⟩ (⟹-to-⟶* rf) (⟹-to-⟶* rg)))
           (⟶-to-⟶* (base snd-pair))
⟹-to-⟶* ⟹-eta-pair         = ⟶-to-⟶* (base eta-pair)
⟹-to-⟶* (⟹-id-left r)      =
  ⟶*-trans (⟶*-∘ʳ (⟹-to-⟶* r)) (⟶-to-⟶* (base id-left))
⟹-to-⟶* (⟹-id-right r)     =
  ⟶*-trans (⟶*-∘ˡ (⟹-to-⟶* r)) (⟶-to-⟶* (base id-right))
