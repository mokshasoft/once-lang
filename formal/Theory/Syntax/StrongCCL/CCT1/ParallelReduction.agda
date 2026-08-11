------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.ParallelReduction
--
-- Parallel reduction for the FULL βη rule set at CCT1 (all β-rules
-- plus η-rules plus structural rules).
--
-- Extends Theory.Syntax.StrongCCL.CCT1.BetaFragment.ParallelReduction
-- (which only handled the β-fragment) with parallel rules for:
--
--   η-rules:   curry-η, curry-apply, curry-compose
--   s-rules:   assoc, pair-dist, eta-pair-gen, term-unique
--
-- The bridge lemmas ⟶βη-to-⟹ and ⟹-to-⟶βη* witness that ⟹ and
-- ⟶βη*  generate the same equivalence on terms — i.e., the
-- multi-step reduction can be packaged into a single parallel step
-- and unpacked back into a finite sequence of single steps.
--
-- This is the foundation for:
--   * a Takahashi-style diamond proof for ⟹ (giving confluence of
--     ⟶βη without going through Newman + local-confluence, which is
--     blocked by the Curien curry-η critical-pair issue);
--   * an SN proof via parallel-reduction-induced reducibility, which
--     would also discharge sn-∘-id (the assoc-reduct issue), Tait's
--     red-all-comp family, and the Red-fst-at-arrow-Prod / -Arrow
--     termination cycle.
--
-- This commit defines ⟹ and the two bridges. The diamond property
-- and the SN application come in subsequent commits.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.ParallelReduction where

open import Theory.Syntax.StrongCCL.CCT1

------------------------------------------------------------------------
-- Parallel reduction.
--
-- Each constructor takes parallel reductions on each subterm and
-- produces a single parallel step. Atomic terms reduce to themselves
-- (reflexivity baked in).  Each β/η/s rule has an analogue that
-- ALSO permits its sub-terms to reduce in parallel.
------------------------------------------------------------------------

data _⟹_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Atomic reflexivity
  ⟹-id       : ∀ {A}   → id {A} ⟹ id
  ⟹-terminal : ∀ {A}   → terminal {A} ⟹ terminal
  ⟹-fst      : ∀ {A B} → fst {A} {B} ⟹ fst
  ⟹-snd      : ∀ {A B} → snd {A} {B} ⟹ snd
  ⟹-apply    : ∀ {A B} → apply {A} {B} ⟹ apply

  -- Structural (congruences)
  ⟹-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
        f ⟹ f' → g ⟹ g' → (f ∘ g) ⟹ (f' ∘ g')
  ⟹-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟹ f' → g ⟹ g' → ⟨ f , g ⟩ ⟹ ⟨ f' , g' ⟩
  ⟹-curry : ∀ {A B C} {f f' : Term (A × B) C} →
            f ⟹ f' → curry f ⟹ curry f'

  -- CCTB β/η rules on CCT1 terms
  ⟹-fst-β : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            f ⟹ f' → g ⟹ g' → (fst ∘ ⟨ f , g ⟩) ⟹ f'
  ⟹-snd-β : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            f ⟹ f' → g ⟹ g' → (snd ∘ ⟨ f , g ⟩) ⟹ g'
  ⟹-eta-pair : ∀ {A B} → ⟨ fst {A} {B} , snd ⟩ ⟹ id
  ⟹-id-left  : ∀ {A B} {f f' : Term A B} → f ⟹ f' → (id ∘ f) ⟹ f'
  ⟹-id-right : ∀ {A B} {f f' : Term A B} → f ⟹ f' → (f ∘ id) ⟹ f'

  -- CCT1 β-rule
  ⟹-curry-β : ∀ {A B C} {f f' : Term (A × B) C} {g g' : Term A B} →
              f ⟹ f' → g ⟹ g' →
              (apply ∘ ⟨ curry f , g ⟩) ⟹ (f' ∘ ⟨ id , g' ⟩)

  -- CCT1 η-rules
  ⟹-curry-η : ∀ {A B C} {f f' : Term A (B ⇒ C)} →
              f ⟹ f' →
              curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟹ f'
  ⟹-curry-apply : ∀ {A B} → curry (apply {A = A} {B = B}) ⟹ id
  ⟹-curry-compose : ∀ {A B C D}
                     {f f' : Term (A × B) C} {g g' : Term D A} →
                     f ⟹ f' → g ⟹ g' →
                     (curry f ∘ g) ⟹ curry (f' ∘ ⟨ g' ∘ fst , snd ⟩)

  -- CCTB s-rules
  ⟹-assoc : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
            f ⟹ f' → g ⟹ g' → h ⟹ h' →
            ((f ∘ g) ∘ h) ⟹ (f' ∘ (g' ∘ h'))
  ⟹-pair-dist : ∀ {A B C D} {f f' : Term C A} {g g' : Term C B} {h h' : Term D C} →
                f ⟹ f' → g ⟹ g' → h ⟹ h' →
                (⟨ f , g ⟩ ∘ h) ⟹ ⟨ f' ∘ h' , g' ∘ h' ⟩
  ⟹-eta-pair-gen : ∀ {A B C} {h h' : Term C (A × B)} →
                   h ⟹ h' → ⟨ fst ∘ h , snd ∘ h ⟩ ⟹ h'
  ⟹-term-unique : ∀ {A B} {f : Term A B} → (terminal ∘ f) ⟹ terminal

infix 4 _⟹_

------------------------------------------------------------------------
-- Reflexivity.
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
-- ⟶βη*-transitivity and congruence lemmas.
------------------------------------------------------------------------

⟶βη*-trans : ∀ {A B} {t u v : Term A B} → t ⟶βη* u → u ⟶βη* v → t ⟶βη* v
⟶βη*-trans done       yz = yz
⟶βη*-trans (r ∷ xy)   yz = r ∷ ⟶βη*-trans xy yz

⟶βη*-∘ˡ : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
          f ⟶βη* f' → (f ∘ g) ⟶βη* (f' ∘ g)
⟶βη*-∘ˡ done       = done
⟶βη*-∘ˡ (r ∷ rs)   = βη-Closure.∘-congˡ r ∷ ⟶βη*-∘ˡ rs

⟶βη*-∘ʳ : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
          g ⟶βη* g' → (f ∘ g) ⟶βη* (f ∘ g')
⟶βη*-∘ʳ done       = done
⟶βη*-∘ʳ (r ∷ rs)   = βη-Closure.∘-congʳ r ∷ ⟶βη*-∘ʳ rs

⟶βη*-⟨,⟩ˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
            f ⟶βη* f' → ⟨ f , g ⟩ ⟶βη* ⟨ f' , g ⟩
⟶βη*-⟨,⟩ˡ done     = done
⟶βη*-⟨,⟩ˡ (r ∷ rs) = βη-Closure.⟨,⟩-congˡ r ∷ ⟶βη*-⟨,⟩ˡ rs

⟶βη*-⟨,⟩ʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
            g ⟶βη* g' → ⟨ f , g ⟩ ⟶βη* ⟨ f , g' ⟩
⟶βη*-⟨,⟩ʳ done     = done
⟶βη*-⟨,⟩ʳ (r ∷ rs) = βη-Closure.⟨,⟩-congʳ r ∷ ⟶βη*-⟨,⟩ʳ rs

⟶βη*-curry : ∀ {A B C} {f f' : Term (A × B) C} →
             f ⟶βη* f' → curry f ⟶βη* curry f'
⟶βη*-curry done     = done
⟶βη*-curry (r ∷ rs) = βη-Closure.curry-cong r ∷ ⟶βη*-curry rs

⟶βη*-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
         f ⟶βη* f' → g ⟶βη* g' → (f ∘ g) ⟶βη* (f' ∘ g')
⟶βη*-∘ ff gg = ⟶βη*-trans (⟶βη*-∘ˡ ff) (⟶βη*-∘ʳ gg)

⟶βη*-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
           f ⟶βη* f' → g ⟶βη* g' → ⟨ f , g ⟩ ⟶βη* ⟨ f' , g' ⟩
⟶βη*-⟨,⟩ ff gg = ⟶βη*-trans (⟶βη*-⟨,⟩ˡ ff) (⟶βη*-⟨,⟩ʳ gg)

⟶βη-to-⟶βη* : ∀ {A B} {f g : Term A B} → f ⟶βη g → f ⟶βη* g
⟶βη-to-⟶βη* r = r ∷ done

------------------------------------------------------------------------
-- Bridge 1: single reduction step → parallel step.
--
-- Each rule (β / η / s) maps to its parallel-reduction analogue with
-- subterms set to reflexivity.  The five congruences lift via ⟹-∘
-- etc.
------------------------------------------------------------------------

⟶βη-to-⟹ : ∀ {A B} {f g : Term A B} → f ⟶βη g → f ⟹ g
-- β-rules
⟶βη-to-⟹ (βη-Closure.base (β-rule (from-CCTB fst-pair))) =
  ⟹-fst-β (⟹-refl _) (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.base (β-rule (from-CCTB snd-pair))) =
  ⟹-snd-β (⟹-refl _) (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.base (β-rule (from-CCTB eta-pair))) =
  ⟹-eta-pair
⟶βη-to-⟹ (βη-Closure.base (β-rule (from-CCTB id-left))) =
  ⟹-id-left (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.base (β-rule (from-CCTB id-right))) =
  ⟹-id-right (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.base (β-rule (from-CCT1 curry-β))) =
  ⟹-curry-β (⟹-refl _) (⟹-refl _)
-- η-rules
⟶βη-to-⟹ (βη-Closure.base (η-rule curry-η)) =
  ⟹-curry-η (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.base (η-rule curry-apply)) =
  ⟹-curry-apply
⟶βη-to-⟹ (βη-Closure.base (η-rule curry-compose)) =
  ⟹-curry-compose (⟹-refl _) (⟹-refl _)
-- s-rules
⟶βη-to-⟹ (βη-Closure.base (s-rule assoc)) =
  ⟹-assoc (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.base (s-rule pair-dist)) =
  ⟹-pair-dist (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.base (s-rule eta-pair-gen)) =
  ⟹-eta-pair-gen (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.base (s-rule term-unique)) =
  ⟹-term-unique
-- congruences
⟶βη-to-⟹ (βη-Closure.∘-congˡ r) = ⟹-∘ (⟶βη-to-⟹ r) (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.∘-congʳ r) = ⟹-∘ (⟹-refl _) (⟶βη-to-⟹ r)
⟶βη-to-⟹ (βη-Closure.⟨,⟩-congˡ r) = ⟹-⟨,⟩ (⟶βη-to-⟹ r) (⟹-refl _)
⟶βη-to-⟹ (βη-Closure.⟨,⟩-congʳ r) = ⟹-⟨,⟩ (⟹-refl _) (⟶βη-to-⟹ r)
⟶βη-to-⟹ (βη-Closure.curry-cong r) = ⟹-curry (⟶βη-to-⟹ r)

------------------------------------------------------------------------
-- Bridge 2: parallel step → multi-step reduction.
--
-- A parallel step reduces all the underlined subterms simultaneously,
-- so we expand it into a sequence: first congruence-reduce every
-- subterm to its target, then fire the corresponding root rule.
------------------------------------------------------------------------

⟹-to-⟶βη* : ∀ {A B} {f g : Term A B} → f ⟹ g → f ⟶βη* g
-- atomic reflexivity
⟹-to-⟶βη* ⟹-id          = done
⟹-to-⟶βη* ⟹-terminal    = done
⟹-to-⟶βη* ⟹-fst         = done
⟹-to-⟶βη* ⟹-snd         = done
⟹-to-⟶βη* ⟹-apply       = done
-- congruences
⟹-to-⟶βη* (⟹-∘ rf rg)   = ⟶βη*-∘ (⟹-to-⟶βη* rf) (⟹-to-⟶βη* rg)
⟹-to-⟶βη* (⟹-⟨,⟩ rf rg) = ⟶βη*-⟨,⟩ (⟹-to-⟶βη* rf) (⟹-to-⟶βη* rg)
⟹-to-⟶βη* (⟹-curry r)   = ⟶βη*-curry (⟹-to-⟶βη* r)
-- β-rules
⟹-to-⟶βη* (⟹-fst-β rf rg) =
  ⟶βη*-trans (⟶βη*-∘ʳ (⟶βη*-⟨,⟩ (⟹-to-⟶βη* rf) (⟹-to-⟶βη* rg)))
              (⟶βη-to-⟶βη* (βη-Closure.base (β-rule (from-CCTB fst-pair))))
⟹-to-⟶βη* (⟹-snd-β rf rg) =
  ⟶βη*-trans (⟶βη*-∘ʳ (⟶βη*-⟨,⟩ (⟹-to-⟶βη* rf) (⟹-to-⟶βη* rg)))
              (⟶βη-to-⟶βη* (βη-Closure.base (β-rule (from-CCTB snd-pair))))
⟹-to-⟶βη* ⟹-eta-pair =
  ⟶βη-to-⟶βη* (βη-Closure.base (β-rule (from-CCTB eta-pair)))
⟹-to-⟶βη* (⟹-id-left r) =
  ⟶βη*-trans (⟶βη*-∘ʳ (⟹-to-⟶βη* r))
              (⟶βη-to-⟶βη* (βη-Closure.base (β-rule (from-CCTB id-left))))
⟹-to-⟶βη* (⟹-id-right r) =
  ⟶βη*-trans (⟶βη*-∘ˡ (⟹-to-⟶βη* r))
              (⟶βη-to-⟶βη* (βη-Closure.base (β-rule (from-CCTB id-right))))
⟹-to-⟶βη* (⟹-curry-β rf rg) =
  ⟶βη*-trans (⟶βη*-∘ʳ (⟶βη*-⟨,⟩ (⟶βη*-curry (⟹-to-⟶βη* rf))
                                  (⟹-to-⟶βη* rg)))
              (⟶βη-to-⟶βη* (βη-Closure.base (β-rule (from-CCT1 curry-β))))
-- η-rules
⟹-to-⟶βη* (⟹-curry-η r) =
  ⟶βη*-trans (⟶βη*-curry (⟶βη*-∘ʳ (⟶βη*-⟨,⟩ˡ (⟶βη*-∘ˡ (⟹-to-⟶βη* r)))))
              (⟶βη-to-⟶βη* (βη-Closure.base (η-rule curry-η)))
⟹-to-⟶βη* ⟹-curry-apply =
  ⟶βη-to-⟶βη* (βη-Closure.base (η-rule curry-apply))
⟹-to-⟶βη* (⟹-curry-compose rf rg) =
  ⟶βη*-trans (⟶βη*-∘ (⟶βη*-curry (⟹-to-⟶βη* rf)) (⟹-to-⟶βη* rg))
              (⟶βη-to-⟶βη* (βη-Closure.base (η-rule curry-compose)))
-- s-rules
⟹-to-⟶βη* (⟹-assoc rf rg rh) =
  ⟶βη*-trans (⟶βη*-∘ (⟶βη*-∘ (⟹-to-⟶βη* rf) (⟹-to-⟶βη* rg))
                       (⟹-to-⟶βη* rh))
              (⟶βη-to-⟶βη* (βη-Closure.base (s-rule assoc)))
⟹-to-⟶βη* (⟹-pair-dist rf rg rh) =
  ⟶βη*-trans (⟶βη*-∘ (⟶βη*-⟨,⟩ (⟹-to-⟶βη* rf) (⟹-to-⟶βη* rg))
                       (⟹-to-⟶βη* rh))
              (⟶βη-to-⟶βη* (βη-Closure.base (s-rule pair-dist)))
⟹-to-⟶βη* (⟹-eta-pair-gen r) =
  ⟶βη*-trans (⟶βη*-⟨,⟩ (⟶βη*-∘ʳ (⟹-to-⟶βη* r)) (⟶βη*-∘ʳ (⟹-to-⟶βη* r)))
              (⟶βη-to-⟶βη* (βη-Closure.base (s-rule eta-pair-gen)))
⟹-to-⟶βη* ⟹-term-unique =
  ⟶βη-to-⟶βη* (βη-Closure.base (s-rule term-unique))
