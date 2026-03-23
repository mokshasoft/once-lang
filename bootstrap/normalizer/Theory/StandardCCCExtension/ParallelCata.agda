------------------------------------------------------------------------
-- ParallelCata: Parallel Cata Reduction Definition
--
-- This module defines parallel cata reduction (_⟹cata_) and basic
-- lemmas that follow directly from the definition.
--
-- This module contains only definitions, no axioms.
------------------------------------------------------------------------

module normalizer.Theory.StandardCCCExtension.ParallelCata where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_];
         terminal; initial; curry; apply; In; Out; cata; fmap;
         _⟶_; _⟶*_; done; step; ⟶*-trans;
         ⟶*-∘-l; ⟶*-∘-r; ⟶*-pair; ⟶*-case; ⟶*-curry; ⟶*-cata; fmap-⟶*)
open import normalizer.Theory.StandardCCCExtension.CataElimination
  using (_⟶cata_; _⟶*cata_; done-cata; step-cata;
         ⟶*cata-trans; ⟶cata→⟶; ⟶*cata→⟶*;
         ⟶*cata-∘-l; ⟶*cata-∘-r; ⟶*cata-pair; ⟶*cata-case;
         ⟶*cata-curry; ⟶*cata-cata;
         cata-β; cata-∘-l; cata-∘-r; cata-pair-l; cata-pair-r;
         cata-case-l; cata-case-r; cata-curry; cata-cata)

open _⟶_
open _⟶cata_

------------------------------------------------------------------------
-- Parallel Cata Reduction
--
-- Like parallel CCC reduction, but only for cata-beta rules.
-- This helps establish the diamond property.
------------------------------------------------------------------------

data _⟹cata_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Reflexivity for atoms
  ⟹cata-id       : ∀ {A} → id {A} ⟹cata id
  ⟹cata-fst      : ∀ {A B} → fst {A} {B} ⟹cata fst
  ⟹cata-snd      : ∀ {A B} → snd {A} {B} ⟹cata snd
  ⟹cata-inl      : ∀ {A B} → inl {A} {B} ⟹cata inl
  ⟹cata-inr      : ∀ {A B} → inr {A} {B} ⟹cata inr
  ⟹cata-terminal : ∀ {A} → terminal {A} ⟹cata terminal
  ⟹cata-initial  : ∀ {A} → initial {A} ⟹cata initial
  ⟹cata-apply    : ∀ {A B} → apply {A} {B} ⟹cata apply
  ⟹cata-In       : ∀ {F} → In {F} ⟹cata In
  ⟹cata-Out      : ∀ {F} → Out {F} ⟹cata Out

  -- Congruence for compound terms
  ⟹cata-∘    : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
               f ⟹cata f' → g ⟹cata g' → (f ∘ g) ⟹cata (f' ∘ g')
  ⟹cata-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
               f ⟹cata f' → g ⟹cata g' → ⟨ f , g ⟩ ⟹cata ⟨ f' , g' ⟩
  ⟹cata-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
               f ⟹cata f' → g ⟹cata g' → [ f , g ] ⟹cata [ f' , g' ]
  ⟹cata-curry : ∀ {A B C} {f f' : Term (A * B) C} →
                f ⟹cata f' → curry f ⟹cata curry f'
  ⟹cata-cata : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
               alg ⟹cata alg' → cata F alg ⟹cata cata F alg'

  -- The cata-beta rule (parallel version)
  ⟹cata-β    : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
               alg ⟹cata alg' →
               (cata F alg ∘ In) ⟹cata (alg' ∘ fmap F (cata F alg'))

------------------------------------------------------------------------
-- Parallel cata reduction is reflexive
------------------------------------------------------------------------

⟹cata-refl : ∀ {A B} (t : Term A B) → t ⟹cata t
⟹cata-refl id = ⟹cata-id
⟹cata-refl (f ∘ g) = ⟹cata-∘ (⟹cata-refl f) (⟹cata-refl g)
⟹cata-refl fst = ⟹cata-fst
⟹cata-refl snd = ⟹cata-snd
⟹cata-refl ⟨ f , g ⟩ = ⟹cata-pair (⟹cata-refl f) (⟹cata-refl g)
⟹cata-refl inl = ⟹cata-inl
⟹cata-refl inr = ⟹cata-inr
⟹cata-refl [ f , g ] = ⟹cata-case (⟹cata-refl f) (⟹cata-refl g)
⟹cata-refl terminal = ⟹cata-terminal
⟹cata-refl initial = ⟹cata-initial
⟹cata-refl (curry f) = ⟹cata-curry (⟹cata-refl f)
⟹cata-refl apply = ⟹cata-apply
⟹cata-refl In = ⟹cata-In
⟹cata-refl Out = ⟹cata-Out
⟹cata-refl (cata F alg) = ⟹cata-cata (⟹cata-refl alg)

------------------------------------------------------------------------
-- Single step implies parallel
------------------------------------------------------------------------

⟶cata→⟹cata : ∀ {A B} {t u : Term A B} → t ⟶cata u → t ⟹cata u
⟶cata→⟹cata cata-β = ⟹cata-β (⟹cata-refl _)
⟶cata→⟹cata (cata-∘-l r) = ⟹cata-∘ (⟶cata→⟹cata r) (⟹cata-refl _)
⟶cata→⟹cata (cata-∘-r r) = ⟹cata-∘ (⟹cata-refl _) (⟶cata→⟹cata r)
⟶cata→⟹cata (cata-pair-l r) = ⟹cata-pair (⟶cata→⟹cata r) (⟹cata-refl _)
⟶cata→⟹cata (cata-pair-r r) = ⟹cata-pair (⟹cata-refl _) (⟶cata→⟹cata r)
⟶cata→⟹cata (cata-case-l r) = ⟹cata-case (⟶cata→⟹cata r) (⟹cata-refl _)
⟶cata→⟹cata (cata-case-r r) = ⟹cata-case (⟹cata-refl _) (⟶cata→⟹cata r)
⟶cata→⟹cata (cata-curry r) = ⟹cata-curry (⟶cata→⟹cata r)
⟶cata→⟹cata (cata-cata r) = ⟹cata-cata (⟶cata→⟹cata r)

------------------------------------------------------------------------
-- Parallel implies multi-step for cata
------------------------------------------------------------------------

⟹cata→⟶*cata : ∀ {A B} {t u : Term A B} → t ⟹cata u → t ⟶*cata u
⟹cata→⟶*cata ⟹cata-id = done-cata
⟹cata→⟶*cata ⟹cata-fst = done-cata
⟹cata→⟶*cata ⟹cata-snd = done-cata
⟹cata→⟶*cata ⟹cata-inl = done-cata
⟹cata→⟶*cata ⟹cata-inr = done-cata
⟹cata→⟶*cata ⟹cata-terminal = done-cata
⟹cata→⟶*cata ⟹cata-initial = done-cata
⟹cata→⟶*cata ⟹cata-apply = done-cata
⟹cata→⟶*cata ⟹cata-In = done-cata
⟹cata→⟶*cata ⟹cata-Out = done-cata
⟹cata→⟶*cata (⟹cata-∘ pf pg) =
  ⟶*cata-trans (⟶*cata-∘-l _ (⟹cata→⟶*cata pf))
               (⟶*cata-∘-r _ (⟹cata→⟶*cata pg))
⟹cata→⟶*cata (⟹cata-pair pf pg) =
  ⟶*cata-pair (⟹cata→⟶*cata pf) (⟹cata→⟶*cata pg)
⟹cata→⟶*cata (⟹cata-case pf pg) =
  ⟶*cata-case (⟹cata→⟶*cata pf) (⟹cata→⟶*cata pg)
⟹cata→⟶*cata (⟹cata-curry pf) =
  ⟶*cata-curry (⟹cata→⟶*cata pf)
⟹cata→⟶*cata (⟹cata-cata palg) =
  ⟶*cata-cata _ (⟹cata→⟶*cata palg)
⟹cata→⟶*cata (⟹cata-β {F} palg) =
  ⟶*cata-trans
    (⟶*cata-∘-l In (⟶*cata-cata F (⟹cata→⟶*cata palg)))
    (step-cata cata-β done-cata)

------------------------------------------------------------------------
-- Reflexive-transitive closure of parallel cata reduction
------------------------------------------------------------------------

data _⟹*cata_ : ∀ {A B} → Term A B → Term A B → Set where
  done⟹cata : ∀ {A B} {t : Term A B} → t ⟹*cata t
  step⟹cata : ∀ {A B} {t u v : Term A B} →
              t ⟹cata u → u ⟹*cata v → t ⟹*cata v

------------------------------------------------------------------------
-- Conversion between ⟶*cata and ⟹*cata
------------------------------------------------------------------------

⟶*cata→⟹*cata : ∀ {A B} {t u : Term A B} → t ⟶*cata u → t ⟹*cata u
⟶*cata→⟹*cata done-cata = done⟹cata
⟶*cata→⟹*cata (step-cata r rs) = step⟹cata (⟶cata→⟹cata r) (⟶*cata→⟹*cata rs)

⟹*cata→⟶*cata : ∀ {A B} {t u : Term A B} → t ⟹*cata u → t ⟶*cata u
⟹*cata→⟶*cata done⟹cata = done-cata
⟹*cata→⟶*cata (step⟹cata p ps) = ⟶*cata-trans (⟹cata→⟶*cata p) (⟹*cata→⟶*cata ps)
