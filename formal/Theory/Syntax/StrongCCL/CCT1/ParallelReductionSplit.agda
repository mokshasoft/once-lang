------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.ParallelReductionSplit
--
-- Hindley-Rosen split of parallel reduction _⟹_ at CCT1 into:
--
--   _⟹₁_  : all rules EXCEPT eta-pair-gen (the linear fragment)
--   _⟹₂_  : reflexivity + congruences + eta-pair-gen ONLY
--
-- The split exists because the eta-pair-gen rule
--
--     ⟨ fst ∘ h , snd ∘ h ⟩  ⟶s  h
--
-- has a non-linear LHS: the SAME h appears twice. This breaks the
-- standard Takahashi-style diamond proof for _⟹_, because a single
-- ⟹-⟨,⟩ congruence step can reduce the two h-copies to syntactically
-- different reducts, destroying the redex pattern even though both
-- copies came from the same source.
--
-- Hindley-Rosen lets us isolate the difficulty: prove diamond for
-- ⟹₁ (where the linear-rule machinery works cleanly) and ⟹₂ (the
-- isolated non-linear rule), prove they commute, and combine via
-- Theory.Derived.HindleyRosen.hindley-rosen to obtain
-- Diamond (⟹₁ ∪ ⟹₂). Then Theory.Derived.ConfluenceFromDiamond
-- gives Confluent (Star (⟹₁ ∪ ⟹₂)), which equals ⟶βη*.
--
-- This module establishes the split, the bridges to ⟹ and ⟶βη, and
-- the union/star-level identification with ⟶βη*.  Diamond ⟹₁,
-- Diamond ⟹₂, and Commute ⟹₁ ⟹₂ are obligations for downstream
-- modules.
--
-- ZERO POSTULATES.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.ParallelReductionSplit where

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.StrongCCL.CCT1.ParallelReduction

------------------------------------------------------------------------
-- _⟹₁_ : parallel reduction WITHOUT eta-pair-gen.
--
-- All ⟹ constructors except ⟹-eta-pair-gen, with the same shapes.
-- Sub-reductions are themselves ⟹₁, not ⟹.
------------------------------------------------------------------------

data _⟹₁_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Atomic reflexivity
  ⟹₁-id       : ∀ {A}   → id {A} ⟹₁ id
  ⟹₁-terminal : ∀ {A}   → terminal {A} ⟹₁ terminal
  ⟹₁-fst      : ∀ {A B} → fst {A} {B} ⟹₁ fst
  ⟹₁-snd      : ∀ {A B} → snd {A} {B} ⟹₁ snd
  ⟹₁-apply    : ∀ {A B} → apply {A} {B} ⟹₁ apply

  -- Structural congruences
  ⟹₁-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
         f ⟹₁ f' → g ⟹₁ g' → (f ∘ g) ⟹₁ (f' ∘ g')
  ⟹₁-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
           f ⟹₁ f' → g ⟹₁ g' → ⟨ f , g ⟩ ⟹₁ ⟨ f' , g' ⟩
  ⟹₁-curry : ∀ {A B C} {f f' : Term (A × B) C} →
             f ⟹₁ f' → curry f ⟹₁ curry f'

  -- CCTB β/η rules
  ⟹₁-fst-β : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
             f ⟹₁ f' → g ⟹₁ g' → (fst ∘ ⟨ f , g ⟩) ⟹₁ f'
  ⟹₁-snd-β : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
             f ⟹₁ f' → g ⟹₁ g' → (snd ∘ ⟨ f , g ⟩) ⟹₁ g'
  ⟹₁-eta-pair : ∀ {A B} → ⟨ fst {A} {B} , snd ⟩ ⟹₁ id
  ⟹₁-id-left  : ∀ {A B} {f f' : Term A B} → f ⟹₁ f' → (id ∘ f) ⟹₁ f'
  ⟹₁-id-right : ∀ {A B} {f f' : Term A B} → f ⟹₁ f' → (f ∘ id) ⟹₁ f'

  -- CCT1 β-rule
  ⟹₁-curry-β : ∀ {A B C} {f f' : Term (A × B) C} {g g' : Term A B} →
               f ⟹₁ f' → g ⟹₁ g' →
               (apply ∘ ⟨ curry f , g ⟩) ⟹₁ (f' ∘ ⟨ id , g' ⟩)

  -- CCT1 η-rules
  ⟹₁-curry-η : ∀ {A B C} {f f' : Term A (B ⇒ C)} →
               f ⟹₁ f' →
               curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟹₁ f'
  ⟹₁-curry-apply : ∀ {A B} → curry (apply {A = A} {B = B}) ⟹₁ id
  ⟹₁-curry-compose : ∀ {A B C D}
                      {f f' : Term (A × B) C} {g g' : Term D A} →
                      f ⟹₁ f' → g ⟹₁ g' →
                      (curry f ∘ g) ⟹₁ curry (f' ∘ ⟨ g' ∘ fst , snd ⟩)

  -- CCTB s-rules — eta-pair-gen DELIBERATELY OMITTED.
  ⟹₁-assoc : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
             f ⟹₁ f' → g ⟹₁ g' → h ⟹₁ h' →
             ((f ∘ g) ∘ h) ⟹₁ (f' ∘ (g' ∘ h'))
  ⟹₁-pair-dist : ∀ {A B C D} {f f' : Term C A} {g g' : Term C B} {h h' : Term D C} →
                 f ⟹₁ f' → g ⟹₁ g' → h ⟹₁ h' →
                 (⟨ f , g ⟩ ∘ h) ⟹₁ ⟨ f' ∘ h' , g' ∘ h' ⟩
  ⟹₁-term-unique : ∀ {A B} {f : Term A B} → (terminal ∘ f) ⟹₁ terminal

infix 4 _⟹₁_

------------------------------------------------------------------------
-- _⟹₂_ : reflexivity + congruences + eta-pair-gen ONLY.
--
-- The minimal sub-relation containing eta-pair-gen and closed under
-- reflexivity and the three structural congruences. No other rule
-- firings.
------------------------------------------------------------------------

data _⟹₂_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Atomic reflexivity
  ⟹₂-id       : ∀ {A}   → id {A} ⟹₂ id
  ⟹₂-terminal : ∀ {A}   → terminal {A} ⟹₂ terminal
  ⟹₂-fst      : ∀ {A B} → fst {A} {B} ⟹₂ fst
  ⟹₂-snd      : ∀ {A B} → snd {A} {B} ⟹₂ snd
  ⟹₂-apply    : ∀ {A B} → apply {A} {B} ⟹₂ apply

  -- Structural congruences
  ⟹₂-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
         f ⟹₂ f' → g ⟹₂ g' → (f ∘ g) ⟹₂ (f' ∘ g')
  ⟹₂-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
           f ⟹₂ f' → g ⟹₂ g' → ⟨ f , g ⟩ ⟹₂ ⟨ f' , g' ⟩
  ⟹₂-curry : ∀ {A B C} {f f' : Term (A × B) C} →
             f ⟹₂ f' → curry f ⟹₂ curry f'

  -- The single non-trivial rule.
  ⟹₂-eta-pair-gen : ∀ {A B C} {h h' : Term C (A × B)} →
                    h ⟹₂ h' → ⟨ fst ∘ h , snd ∘ h ⟩ ⟹₂ h'

infix 4 _⟹₂_

------------------------------------------------------------------------
-- Reflexivity for ⟹₁ and ⟹₂.
------------------------------------------------------------------------

⟹₁-refl : ∀ {A B} (t : Term A B) → t ⟹₁ t
⟹₁-refl id          = ⟹₁-id
⟹₁-refl terminal    = ⟹₁-terminal
⟹₁-refl fst         = ⟹₁-fst
⟹₁-refl snd         = ⟹₁-snd
⟹₁-refl apply       = ⟹₁-apply
⟹₁-refl (f ∘ g)     = ⟹₁-∘ (⟹₁-refl f) (⟹₁-refl g)
⟹₁-refl ⟨ f , g ⟩   = ⟹₁-⟨,⟩ (⟹₁-refl f) (⟹₁-refl g)
⟹₁-refl (curry f)   = ⟹₁-curry (⟹₁-refl f)

⟹₂-refl : ∀ {A B} (t : Term A B) → t ⟹₂ t
⟹₂-refl id          = ⟹₂-id
⟹₂-refl terminal    = ⟹₂-terminal
⟹₂-refl fst         = ⟹₂-fst
⟹₂-refl snd         = ⟹₂-snd
⟹₂-refl apply       = ⟹₂-apply
⟹₂-refl (f ∘ g)     = ⟹₂-∘ (⟹₂-refl f) (⟹₂-refl g)
⟹₂-refl ⟨ f , g ⟩   = ⟹₂-⟨,⟩ (⟹₂-refl f) (⟹₂-refl g)
⟹₂-refl (curry f)   = ⟹₂-curry (⟹₂-refl f)

------------------------------------------------------------------------
-- Bridge: ⟹₁ ⊆ ⟹.
------------------------------------------------------------------------

⟹₁-to-⟹ : ∀ {A B} {t u : Term A B} → t ⟹₁ u → t ⟹ u
⟹₁-to-⟹ ⟹₁-id                 = ⟹-id
⟹₁-to-⟹ ⟹₁-terminal           = ⟹-terminal
⟹₁-to-⟹ ⟹₁-fst                = ⟹-fst
⟹₁-to-⟹ ⟹₁-snd                = ⟹-snd
⟹₁-to-⟹ ⟹₁-apply              = ⟹-apply
⟹₁-to-⟹ (⟹₁-∘ rf rg)          = ⟹-∘ (⟹₁-to-⟹ rf) (⟹₁-to-⟹ rg)
⟹₁-to-⟹ (⟹₁-⟨,⟩ rf rg)        = ⟹-⟨,⟩ (⟹₁-to-⟹ rf) (⟹₁-to-⟹ rg)
⟹₁-to-⟹ (⟹₁-curry r)          = ⟹-curry (⟹₁-to-⟹ r)
⟹₁-to-⟹ (⟹₁-fst-β rf rg)      = ⟹-fst-β (⟹₁-to-⟹ rf) (⟹₁-to-⟹ rg)
⟹₁-to-⟹ (⟹₁-snd-β rf rg)      = ⟹-snd-β (⟹₁-to-⟹ rf) (⟹₁-to-⟹ rg)
⟹₁-to-⟹ ⟹₁-eta-pair           = ⟹-eta-pair
⟹₁-to-⟹ (⟹₁-id-left r)        = ⟹-id-left (⟹₁-to-⟹ r)
⟹₁-to-⟹ (⟹₁-id-right r)       = ⟹-id-right (⟹₁-to-⟹ r)
⟹₁-to-⟹ (⟹₁-curry-β rf rg)    = ⟹-curry-β (⟹₁-to-⟹ rf) (⟹₁-to-⟹ rg)
⟹₁-to-⟹ (⟹₁-curry-η r)        = ⟹-curry-η (⟹₁-to-⟹ r)
⟹₁-to-⟹ ⟹₁-curry-apply        = ⟹-curry-apply
⟹₁-to-⟹ (⟹₁-curry-compose rf rg) =
  ⟹-curry-compose (⟹₁-to-⟹ rf) (⟹₁-to-⟹ rg)
⟹₁-to-⟹ (⟹₁-assoc rf rg rh)    =
  ⟹-assoc (⟹₁-to-⟹ rf) (⟹₁-to-⟹ rg) (⟹₁-to-⟹ rh)
⟹₁-to-⟹ (⟹₁-pair-dist rf rg rh) =
  ⟹-pair-dist (⟹₁-to-⟹ rf) (⟹₁-to-⟹ rg) (⟹₁-to-⟹ rh)
⟹₁-to-⟹ ⟹₁-term-unique         = ⟹-term-unique

------------------------------------------------------------------------
-- Bridge: ⟹₂ ⊆ ⟹.
------------------------------------------------------------------------

⟹₂-to-⟹ : ∀ {A B} {t u : Term A B} → t ⟹₂ u → t ⟹ u
⟹₂-to-⟹ ⟹₂-id              = ⟹-id
⟹₂-to-⟹ ⟹₂-terminal        = ⟹-terminal
⟹₂-to-⟹ ⟹₂-fst             = ⟹-fst
⟹₂-to-⟹ ⟹₂-snd             = ⟹-snd
⟹₂-to-⟹ ⟹₂-apply           = ⟹-apply
⟹₂-to-⟹ (⟹₂-∘ rf rg)       = ⟹-∘ (⟹₂-to-⟹ rf) (⟹₂-to-⟹ rg)
⟹₂-to-⟹ (⟹₂-⟨,⟩ rf rg)     = ⟹-⟨,⟩ (⟹₂-to-⟹ rf) (⟹₂-to-⟹ rg)
⟹₂-to-⟹ (⟹₂-curry r)       = ⟹-curry (⟹₂-to-⟹ r)
⟹₂-to-⟹ (⟹₂-eta-pair-gen r) = ⟹-eta-pair-gen (⟹₂-to-⟹ r)

------------------------------------------------------------------------
-- Bridge: ⟹₁ ⊆ ⟶βη*  and  ⟹₂ ⊆ ⟶βη*  (factor through ⟹).
------------------------------------------------------------------------

⟹₁-to-⟶βη* : ∀ {A B} {t u : Term A B} → t ⟹₁ u → t ⟶βη* u
⟹₁-to-⟶βη* r = ⟹-to-⟶βη* (⟹₁-to-⟹ r)

⟹₂-to-⟶βη* : ∀ {A B} {t u : Term A B} → t ⟹₂ u → t ⟶βη* u
⟹₂-to-⟶βη* r = ⟹-to-⟶βη* (⟹₂-to-⟹ r)

------------------------------------------------------------------------
-- Bridge: ⟶βη single step → (⟹₁ ⊎ ⟹₂).
--
-- Each individual rule fits cleanly in exactly one component:
--   * eta-pair-gen → ⟹₂ (only, by construction)
--   * everything else → ⟹₁
-- Congruences are handled by the corresponding ⟹₁ congruences (since
-- a ⟶βη single step has all-but-one-position reflexive, and each
-- congruence in ⟹₁ admits ⟹₁-refl on the unchanged subterm).
------------------------------------------------------------------------

⟶βη-to-⟹₁⊎⟹₂ : ∀ {A B} {t u : Term A B} →
                t ⟶βη u → (t ⟹₁ u) ⊎ (t ⟹₂ u)
-- β-rules
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (β-rule (from-CCTB fst-pair))) =
  inj₁ (⟹₁-fst-β (⟹₁-refl _) (⟹₁-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (β-rule (from-CCTB snd-pair))) =
  inj₁ (⟹₁-snd-β (⟹₁-refl _) (⟹₁-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (β-rule (from-CCTB eta-pair))) =
  inj₁ ⟹₁-eta-pair
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (β-rule (from-CCTB id-left))) =
  inj₁ (⟹₁-id-left (⟹₁-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (β-rule (from-CCTB id-right))) =
  inj₁ (⟹₁-id-right (⟹₁-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (β-rule (from-CCT1 curry-β))) =
  inj₁ (⟹₁-curry-β (⟹₁-refl _) (⟹₁-refl _))
-- η-rules
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (η-rule curry-η)) =
  inj₁ (⟹₁-curry-η (⟹₁-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (η-rule curry-apply)) =
  inj₁ ⟹₁-curry-apply
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (η-rule curry-compose)) =
  inj₁ (⟹₁-curry-compose (⟹₁-refl _) (⟹₁-refl _))
-- s-rules — eta-pair-gen routes to ⟹₂.
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (s-rule assoc)) =
  inj₁ (⟹₁-assoc (⟹₁-refl _) (⟹₁-refl _) (⟹₁-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (s-rule pair-dist)) =
  inj₁ (⟹₁-pair-dist (⟹₁-refl _) (⟹₁-refl _) (⟹₁-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (s-rule eta-pair-gen)) =
  inj₂ (⟹₂-eta-pair-gen (⟹₂-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.base (s-rule term-unique)) =
  inj₁ ⟹₁-term-unique
-- Congruences — the inner step routes to ⟹₁ or ⟹₂; either way, lift
-- via the corresponding ⟹ᵢ congruence with refl on the other side.
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.∘-congˡ r) with ⟶βη-to-⟹₁⊎⟹₂ r
... | inj₁ r₁ = inj₁ (⟹₁-∘ r₁ (⟹₁-refl _))
... | inj₂ r₂ = inj₂ (⟹₂-∘ r₂ (⟹₂-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.∘-congʳ r) with ⟶βη-to-⟹₁⊎⟹₂ r
... | inj₁ r₁ = inj₁ (⟹₁-∘ (⟹₁-refl _) r₁)
... | inj₂ r₂ = inj₂ (⟹₂-∘ (⟹₂-refl _) r₂)
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.⟨,⟩-congˡ r) with ⟶βη-to-⟹₁⊎⟹₂ r
... | inj₁ r₁ = inj₁ (⟹₁-⟨,⟩ r₁ (⟹₁-refl _))
... | inj₂ r₂ = inj₂ (⟹₂-⟨,⟩ r₂ (⟹₂-refl _))
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.⟨,⟩-congʳ r) with ⟶βη-to-⟹₁⊎⟹₂ r
... | inj₁ r₁ = inj₁ (⟹₁-⟨,⟩ (⟹₁-refl _) r₁)
... | inj₂ r₂ = inj₂ (⟹₂-⟨,⟩ (⟹₂-refl _) r₂)
⟶βη-to-⟹₁⊎⟹₂ (βη-Closure.curry-cong r) with ⟶βη-to-⟹₁⊎⟹₂ r
... | inj₁ r₁ = inj₁ (⟹₁-curry r₁)
... | inj₂ r₂ = inj₂ (⟹₂-curry r₂)
