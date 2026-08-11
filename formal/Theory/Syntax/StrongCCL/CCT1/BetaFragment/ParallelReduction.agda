------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.BetaFragment.ParallelReduction
--
-- Parallel reduction at CCT1, and its bridges with _⟶*_.
-- Extends the CCTB pattern with curry/apply generators and curry β/η.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.BetaFragment.ParallelReduction where

open import Theory.Syntax.StrongCCL.CCT1.BetaFragment

------------------------------------------------------------------------
-- Parallel reduction
------------------------------------------------------------------------

data _⟹_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Atomic reflexivity
  ⟹-id       : ∀ {A}   → id {A} ⟹ id
  ⟹-terminal : ∀ {A}   → terminal {A} ⟹ terminal
  ⟹-fst      : ∀ {A B} → fst {A} {B} ⟹ fst
  ⟹-snd      : ∀ {A B} → snd {A} {B} ⟹ snd
  ⟹-apply    : ∀ {A B} → apply {A} {B} ⟹ apply

  -- Structural
  ⟹-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
        f ⟹ f' → g ⟹ g' → (f ∘ g) ⟹ (f' ∘ g')
  ⟹-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟹ f' → g ⟹ g' → ⟨ f , g ⟩ ⟹ ⟨ f' , g' ⟩
  ⟹-curry : ∀ {A B C} {f f' : Term (A × B) C} →
            f ⟹ f' → curry f ⟹ curry f'

  -- CCTB β/η on CCT1 terms
  ⟹-fst-β : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            f ⟹ f' → g ⟹ g' → (fst ∘ ⟨ f , g ⟩) ⟹ f'
  ⟹-snd-β : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            f ⟹ f' → g ⟹ g' → (snd ∘ ⟨ f , g ⟩) ⟹ g'
  ⟹-eta-pair : ∀ {A B} → ⟨ fst {A} {B} , snd ⟩ ⟹ id
  ⟹-id-left  : ∀ {A B} {f f' : Term A B} → f ⟹ f' → (id ∘ f) ⟹ f'
  ⟹-id-right : ∀ {A B} {f f' : Term A B} → f ⟹ f' → (f ∘ id) ⟹ f'

  -- CCT1 new: curry β (η omitted — see BaseRules for rationale)
  ⟹-curry-β : ∀ {A B C} {f f' : Term (A × B) C} {g g' : Term A B} →
              f ⟹ f' → g ⟹ g' →
              (apply ∘ ⟨ curry f , g ⟩) ⟹ (f' ∘ ⟨ id , g' ⟩)

infix 4 _⟹_

------------------------------------------------------------------------
-- Reflexivity
------------------------------------------------------------------------

⟹-refl : ∀ {A B} (t : Term A B) → t ⟹ t
⟹-refl id          = ⟹-id
⟹-refl terminal    = ⟹-terminal
⟹-refl fst         = ⟹-fst
⟹-refl snd         = ⟹-snd
⟹-refl apply       = ⟹-apply
⟹-refl (f ∘ g)     = ⟹-∘ (⟹-refl f) (⟹-refl g)
⟹-refl ⟨ f , g ⟩   = ⟹-⟨,⟩ (⟹-refl f) (⟹-refl g)
⟹-refl (curry f)   = ⟹-curry (⟹-refl f)

------------------------------------------------------------------------
-- ⟶*-transitivity and congruence lemmas
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

⟶*-curry : ∀ {A B C} {f f' : Term (A × B) C} →
           f ⟶* f' → curry f ⟶* curry f'
⟶*-curry done     = done
⟶*-curry (r ∷ rs) = curry-cong r ∷ ⟶*-curry rs

⟶*-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
       f ⟶* f' → g ⟶* g' → (f ∘ g) ⟶* (f' ∘ g')
⟶*-∘ ff gg = ⟶*-trans (⟶*-∘ˡ ff) (⟶*-∘ʳ gg)

⟶*-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
         f ⟶* f' → g ⟶* g' → ⟨ f , g ⟩ ⟶* ⟨ f' , g' ⟩
⟶*-⟨,⟩ ff gg = ⟶*-trans (⟶*-⟨,⟩ˡ ff) (⟶*-⟨,⟩ʳ gg)

⟶-to-⟶* : ∀ {A B} {f g : Term A B} → f ⟶ g → f ⟶* g
⟶-to-⟶* r = r ∷ done

------------------------------------------------------------------------
-- Bridge 1: single reduction step → parallel step
--
-- Each CCT1 reduction rule (from base + congruences) maps to a
-- parallel reduction rule with sub-terms left as reflexivity.
------------------------------------------------------------------------

⟶-to-⟹ : ∀ {A B} {f g : Term A B} → f ⟶ g → f ⟹ g
⟶-to-⟹ (base (from-CCTB fst-pair))      = ⟹-fst-β (⟹-refl _) (⟹-refl _)
⟶-to-⟹ (base (from-CCTB snd-pair))      = ⟹-snd-β (⟹-refl _) (⟹-refl _)
⟶-to-⟹ (base (from-CCTB eta-pair))      = ⟹-eta-pair
⟶-to-⟹ (base (from-CCTB id-left))       = ⟹-id-left (⟹-refl _)
⟶-to-⟹ (base (from-CCTB id-right))      = ⟹-id-right (⟹-refl _)
⟶-to-⟹ (base (from-CCT1 curry-β))       = ⟹-curry-β (⟹-refl _) (⟹-refl _)
⟶-to-⟹ (∘-congˡ r)                      = ⟹-∘ (⟶-to-⟹ r) (⟹-refl _)
⟶-to-⟹ (∘-congʳ r)                      = ⟹-∘ (⟹-refl _) (⟶-to-⟹ r)
⟶-to-⟹ (⟨,⟩-congˡ r)                    = ⟹-⟨,⟩ (⟶-to-⟹ r) (⟹-refl _)
⟶-to-⟹ (⟨,⟩-congʳ r)                    = ⟹-⟨,⟩ (⟹-refl _) (⟶-to-⟹ r)
⟶-to-⟹ (curry-cong r)                   = ⟹-curry (⟶-to-⟹ r)

------------------------------------------------------------------------
-- Bridge 2: parallel step → reduction sequence
------------------------------------------------------------------------

⟹-to-⟶* : ∀ {A B} {f g : Term A B} → f ⟹ g → f ⟶* g
⟹-to-⟶* ⟹-id          = done
⟹-to-⟶* ⟹-terminal    = done
⟹-to-⟶* ⟹-fst         = done
⟹-to-⟶* ⟹-snd         = done
⟹-to-⟶* ⟹-apply       = done
⟹-to-⟶* (⟹-∘ rf rg)   = ⟶*-∘ (⟹-to-⟶* rf) (⟹-to-⟶* rg)
⟹-to-⟶* (⟹-⟨,⟩ rf rg) = ⟶*-⟨,⟩ (⟹-to-⟶* rf) (⟹-to-⟶* rg)
⟹-to-⟶* (⟹-curry r)   = ⟶*-curry (⟹-to-⟶* r)
⟹-to-⟶* (⟹-fst-β rf rg) =
  ⟶*-trans (⟶*-∘ʳ (⟶*-⟨,⟩ (⟹-to-⟶* rf) (⟹-to-⟶* rg)))
           (⟶-to-⟶* (base (from-CCTB fst-pair)))
⟹-to-⟶* (⟹-snd-β rf rg) =
  ⟶*-trans (⟶*-∘ʳ (⟶*-⟨,⟩ (⟹-to-⟶* rf) (⟹-to-⟶* rg)))
           (⟶-to-⟶* (base (from-CCTB snd-pair)))
⟹-to-⟶* ⟹-eta-pair      = ⟶-to-⟶* (base (from-CCTB eta-pair))
⟹-to-⟶* (⟹-id-left r)   =
  ⟶*-trans (⟶*-∘ʳ (⟹-to-⟶* r)) (⟶-to-⟶* (base (from-CCTB id-left)))
⟹-to-⟶* (⟹-id-right r)  =
  ⟶*-trans (⟶*-∘ˡ (⟹-to-⟶* r)) (⟶-to-⟶* (base (from-CCTB id-right)))
⟹-to-⟶* (⟹-curry-β rf rg) =
  ⟶*-trans (⟶*-∘ʳ (⟶*-⟨,⟩ (⟶*-curry (⟹-to-⟶* rf)) (⟹-to-⟶* rg)))
           (⟶-to-⟶* (base (from-CCT1 curry-β)))
