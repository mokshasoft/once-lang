------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.HardinSplit
--
-- Hardin 1989's R₁/R₂ split, mechanised as sub-relations of ⟶βη.
--
--   R₁ = 𝒢 = { assoc, pair-dist, fst-pair, snd-pair, curry-β,
--             id-right-fst, id-right-snd }
--
--   R₂ = the remaining rules:
--        { id-left, id-right-residual (LHS not fst/snd),
--          eta-pair, eta-pair-gen, term-unique,
--          curry-η, curry-apply, curry-compose }
--
-- KEY DEPARTURE from Option B (RuleSplit.agda):
--   id-right is SPLIT: only its fst/snd instances live in R₁; the
--   curry/composition/pair/terminal/apply/id instances live in R₂.
--   This is the crucial Hardin trick — it makes R₁ free of the
--   curry-compose × id-right critical pair (because R₁ doesn't have
--   curry-compose at all, only curry-β).
--
-- ZERO POSTULATES.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.HardinSplit where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.CongruenceClosure

------------------------------------------------------------------------
-- R₁-rules : Hardin's 𝒢.
--
-- Note the explicit fst-id, snd-id constructors. They embed two
-- specific instances of the general id-right rule, forcing R₁ to
-- only fire id-right at these atomic LHS shapes.
------------------------------------------------------------------------

data _⟶R₁-rules_ : ∀ {A B} → Term A B → Term A B → Set where
  -- From β:
  fst-pair : ∀ {A B C} {f : Term C A} {g : Term C B} →
             (fst ∘ ⟨ f , g ⟩) ⟶R₁-rules f
  snd-pair : ∀ {A B C} {f : Term C A} {g : Term C B} →
             (snd ∘ ⟨ f , g ⟩) ⟶R₁-rules g
  curry-β  : ∀ {A B C} {f : Term (A × B) C} {g : Term A B} →
             (apply ∘ ⟨ curry f , g ⟩) ⟶R₁-rules (f ∘ ⟨ id , g ⟩)
  fst-id   : ∀ {A B} → (fst {A} {B} ∘ id) ⟶R₁-rules fst
  snd-id   : ∀ {A B} → (snd {A} {B} ∘ id) ⟶R₁-rules snd
  -- From s:
  assoc        : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                 ((f ∘ g) ∘ h) ⟶R₁-rules (f ∘ (g ∘ h))
  pair-dist    : ∀ {A B C D} {f : Term C A} {g : Term C B} {h : Term D C} →
                 (⟨ f , g ⟩ ∘ h) ⟶R₁-rules ⟨ f ∘ h , g ∘ h ⟩

infix 4 _⟶R₁-rules_

------------------------------------------------------------------------
-- R₂-rules : the residual.
--
-- id-right-residual carries an explicit guard: its LHS must NOT be
-- fst/snd (those are handled by fst-id/snd-id in R₁).  We encode the
-- guard as an inductive family: id-right-residual is allowed at
-- specific LHS shapes (id, apply, terminal, composition, pair, curry).
------------------------------------------------------------------------

-- LHS shapes admissible for residual id-right (the "not fst/snd" cases).
data IdRightLHS : ∀ {A B} → Term A B → Set where
  iridR-id       : ∀ {A}            → IdRightLHS (id {A})
  iridR-apply    : ∀ {A B}          → IdRightLHS (apply {A} {B})
  iridR-terminal : ∀ {A}            → IdRightLHS (terminal {A})
  iridR-comp     : ∀ {A B C}
                   (h : Term B C) (k : Term A B) → IdRightLHS (h ∘ k)
  iridR-pair     : ∀ {A B C}
                   (h : Term C A) (k : Term C B) → IdRightLHS ⟨ h , k ⟩
  iridR-curry    : ∀ {A B C}
                   (h : Term (A × B) C) → IdRightLHS (curry h)

data _⟶R₂-rules_ : ∀ {A B} → Term A B → Term A B → Set where
  -- From β: id-left (always), eta-pair, residual id-right.
  id-left      : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶R₂-rules f
  eta-pair     : ∀ {A B} → ⟨ fst {A} {B} , snd ⟩ ⟶R₂-rules id
  id-right-res : ∀ {A B} {f : Term A B} → IdRightLHS f → (f ∘ id) ⟶R₂-rules f
  -- From s: eta-pair-gen, term-unique.
  eta-pair-gen : ∀ {A B C} {h : Term C (A × B)} →
                 ⟨ fst ∘ h , snd ∘ h ⟩ ⟶R₂-rules h
  term-unique  : ∀ {A B} {f : Term A B} → (terminal ∘ f) ⟶R₂-rules terminal
  -- From η:
  curry-η      : ∀ {A B C} {f : Term A (B ⇒ C)} →
                 curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟶R₂-rules f
  curry-apply  : ∀ {A B} → curry (apply {A = A} {B = B}) ⟶R₂-rules id
  curry-comp   : ∀ {A B C D} {f : Term (A × B) C} {g : Term D A} →
                 (curry f ∘ g) ⟶R₂-rules curry (f ∘ ⟨ g ∘ fst , snd ⟩)

infix 4 _⟶R₂-rules_

------------------------------------------------------------------------
-- Congruence closures.
------------------------------------------------------------------------

module R₁-Closure =
  CCT1-Close Ty _×_ _⇒_ Term _∘_ ⟨_,_⟩ curry _⟶R₁-rules_

_⟶R₁_ : ∀ {A B} → Term A B → Term A B → Set
_⟶R₁_ = R₁-Closure.Closed

infix 4 _⟶R₁_

module R₂-Closure =
  CCT1-Close Ty _×_ _⇒_ Term _∘_ ⟨_,_⟩ curry _⟶R₂-rules_

_⟶R₂_ : ∀ {A B} → Term A B → Term A B → Set
_⟶R₂_ = R₂-Closure.Closed

infix 4 _⟶R₂_

------------------------------------------------------------------------
-- Bridge: ⟶R₁ ⊆ ⟶βη.
------------------------------------------------------------------------

R₁-rules-to-βη-rules : ∀ {A B} {f g : Term A B} →
                       f ⟶R₁-rules g → f ⟶βη-rules g
R₁-rules-to-βη-rules fst-pair  = β-rule (from-CCTB fst-pair)
R₁-rules-to-βη-rules snd-pair  = β-rule (from-CCTB snd-pair)
R₁-rules-to-βη-rules curry-β   = β-rule (from-CCT1 curry-β)
R₁-rules-to-βη-rules fst-id    = β-rule (from-CCTB id-right)
R₁-rules-to-βη-rules snd-id    = β-rule (from-CCTB id-right)
R₁-rules-to-βη-rules assoc     = s-rule assoc
R₁-rules-to-βη-rules pair-dist = s-rule pair-dist

⟶R₁-to-⟶βη : ∀ {A B} {t u : Term A B} → t ⟶R₁ u → t ⟶βη u
⟶R₁-to-⟶βη (R₁-Closure.base r)        = βη-Closure.base (R₁-rules-to-βη-rules r)
⟶R₁-to-⟶βη (R₁-Closure.∘-congˡ r)     = βη-Closure.∘-congˡ (⟶R₁-to-⟶βη r)
⟶R₁-to-⟶βη (R₁-Closure.∘-congʳ r)     = βη-Closure.∘-congʳ (⟶R₁-to-⟶βη r)
⟶R₁-to-⟶βη (R₁-Closure.⟨,⟩-congˡ r)   = βη-Closure.⟨,⟩-congˡ (⟶R₁-to-⟶βη r)
⟶R₁-to-⟶βη (R₁-Closure.⟨,⟩-congʳ r)   = βη-Closure.⟨,⟩-congʳ (⟶R₁-to-⟶βη r)
⟶R₁-to-⟶βη (R₁-Closure.curry-cong r)  = βη-Closure.curry-cong (⟶R₁-to-⟶βη r)

------------------------------------------------------------------------
-- Bridge: ⟶R₂ ⊆ ⟶βη.
------------------------------------------------------------------------

R₂-rules-to-βη-rules : ∀ {A B} {f g : Term A B} →
                       f ⟶R₂-rules g → f ⟶βη-rules g
R₂-rules-to-βη-rules id-left          = β-rule (from-CCTB id-left)
R₂-rules-to-βη-rules eta-pair         = β-rule (from-CCTB eta-pair)
R₂-rules-to-βη-rules (id-right-res _) = β-rule (from-CCTB id-right)
R₂-rules-to-βη-rules eta-pair-gen     = s-rule eta-pair-gen
R₂-rules-to-βη-rules term-unique      = s-rule term-unique
R₂-rules-to-βη-rules curry-η          = η-rule curry-η
R₂-rules-to-βη-rules curry-apply      = η-rule curry-apply
R₂-rules-to-βη-rules curry-comp       = η-rule curry-compose

⟶R₂-to-⟶βη : ∀ {A B} {t u : Term A B} → t ⟶R₂ u → t ⟶βη u
⟶R₂-to-⟶βη (R₂-Closure.base r)        = βη-Closure.base (R₂-rules-to-βη-rules r)
⟶R₂-to-⟶βη (R₂-Closure.∘-congˡ r)     = βη-Closure.∘-congˡ (⟶R₂-to-⟶βη r)
⟶R₂-to-⟶βη (R₂-Closure.∘-congʳ r)     = βη-Closure.∘-congʳ (⟶R₂-to-⟶βη r)
⟶R₂-to-⟶βη (R₂-Closure.⟨,⟩-congˡ r)   = βη-Closure.⟨,⟩-congˡ (⟶R₂-to-⟶βη r)
⟶R₂-to-⟶βη (R₂-Closure.⟨,⟩-congʳ r)   = βη-Closure.⟨,⟩-congʳ (⟶R₂-to-⟶βη r)
⟶R₂-to-⟶βη (R₂-Closure.curry-cong r)  = βη-Closure.curry-cong (⟶R₂-to-⟶βη r)

------------------------------------------------------------------------
-- Bridge: ⟶βη single step → ⟶R₁ ⊎ ⟶R₂.
--
-- Each ⟶βη rule maps to exactly one of R₁/R₂, except id-right which
-- routes by case-analysis on its LHS shape.
------------------------------------------------------------------------

-- Helper: dispatch on the LHS of an id-right step.
id-right-dispatch :
  ∀ {A B} (f : Term A B) → (f ∘ id) ⟶R₁ f ⊎ (f ∘ id) ⟶R₂ f
id-right-dispatch id          =
  inj₂ (R₂-Closure.base (id-right-res iridR-id))
id-right-dispatch fst         =
  inj₁ (R₁-Closure.base fst-id)
id-right-dispatch snd         =
  inj₁ (R₁-Closure.base snd-id)
id-right-dispatch apply       =
  inj₂ (R₂-Closure.base (id-right-res iridR-apply))
id-right-dispatch terminal    =
  inj₂ (R₂-Closure.base (id-right-res iridR-terminal))
id-right-dispatch (h ∘ k)     =
  inj₂ (R₂-Closure.base (id-right-res (iridR-comp h k)))
id-right-dispatch ⟨ h , k ⟩   =
  inj₂ (R₂-Closure.base (id-right-res (iridR-pair h k)))
id-right-dispatch (curry h)   =
  inj₂ (R₂-Closure.base (id-right-res (iridR-curry h)))

⟶βη-to-R₁⊎R₂ : ∀ {A B} {t u : Term A B} →
                t ⟶βη u → (t ⟶R₁ u) ⊎ (t ⟶R₂ u)
-- β-rules:
⟶βη-to-R₁⊎R₂ (βη-Closure.base (β-rule (from-CCTB fst-pair))) =
  inj₁ (R₁-Closure.base fst-pair)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (β-rule (from-CCTB snd-pair))) =
  inj₁ (R₁-Closure.base snd-pair)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (β-rule (from-CCTB eta-pair))) =
  inj₂ (R₂-Closure.base eta-pair)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (β-rule (from-CCTB id-left))) =
  inj₂ (R₂-Closure.base id-left)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (β-rule (from-CCTB (id-right {f = f})))) =
  id-right-dispatch f
⟶βη-to-R₁⊎R₂ (βη-Closure.base (β-rule (from-CCT1 curry-β))) =
  inj₁ (R₁-Closure.base curry-β)
-- η-rules:
⟶βη-to-R₁⊎R₂ (βη-Closure.base (η-rule curry-η)) =
  inj₂ (R₂-Closure.base curry-η)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (η-rule curry-apply)) =
  inj₂ (R₂-Closure.base curry-apply)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (η-rule curry-compose)) =
  inj₂ (R₂-Closure.base curry-comp)
-- s-rules:
⟶βη-to-R₁⊎R₂ (βη-Closure.base (s-rule assoc)) =
  inj₁ (R₁-Closure.base assoc)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (s-rule pair-dist)) =
  inj₁ (R₁-Closure.base pair-dist)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (s-rule eta-pair-gen)) =
  inj₂ (R₂-Closure.base eta-pair-gen)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (s-rule term-unique)) =
  inj₂ (R₂-Closure.base term-unique)
-- Congruences:
⟶βη-to-R₁⊎R₂ (βη-Closure.∘-congˡ r) with ⟶βη-to-R₁⊎R₂ r
... | inj₁ r₁ = inj₁ (R₁-Closure.∘-congˡ r₁)
... | inj₂ r₂ = inj₂ (R₂-Closure.∘-congˡ r₂)
⟶βη-to-R₁⊎R₂ (βη-Closure.∘-congʳ r) with ⟶βη-to-R₁⊎R₂ r
... | inj₁ r₁ = inj₁ (R₁-Closure.∘-congʳ r₁)
... | inj₂ r₂ = inj₂ (R₂-Closure.∘-congʳ r₂)
⟶βη-to-R₁⊎R₂ (βη-Closure.⟨,⟩-congˡ r) with ⟶βη-to-R₁⊎R₂ r
... | inj₁ r₁ = inj₁ (R₁-Closure.⟨,⟩-congˡ r₁)
... | inj₂ r₂ = inj₂ (R₂-Closure.⟨,⟩-congˡ r₂)
⟶βη-to-R₁⊎R₂ (βη-Closure.⟨,⟩-congʳ r) with ⟶βη-to-R₁⊎R₂ r
... | inj₁ r₁ = inj₁ (R₁-Closure.⟨,⟩-congʳ r₁)
... | inj₂ r₂ = inj₂ (R₂-Closure.⟨,⟩-congʳ r₂)
⟶βη-to-R₁⊎R₂ (βη-Closure.curry-cong r) with ⟶βη-to-R₁⊎R₂ r
... | inj₁ r₁ = inj₁ (R₁-Closure.curry-cong r₁)
... | inj₂ r₂ = inj₂ (R₂-Closure.curry-cong r₂)
