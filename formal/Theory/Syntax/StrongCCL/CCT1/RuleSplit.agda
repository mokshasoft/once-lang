------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.RuleSplit
--
-- The Di Cosmo R₁/R₂ split of CCT1's βη rule set:
--
--   R₁ = β-rules ∪ s-rules
--        { fst-pair, snd-pair, eta-pair, id-left, id-right, curry-β,
--          assoc, pair-dist, eta-pair-gen, term-unique }
--   R₂ = η-rules
--        { curry-η, curry-apply, curry-compose }
--
-- This is "Option B" from plans/cct1-confluence-dicosmo.md:
--
--   * R₁ is the SN sub-system (Tait-friendly, β + structural).
--   * R₂ is the η fragment (the rules that interact with R₁'s nfs in
--     the curry-compose / id-right critical pair).
--
-- Defines:
--   _⟶R₁_         : congruence closure of R₁'s rules
--   _⟶R₂_         : congruence closure of R₂'s rules
--   _⟶R₁*_, _⟶R₂*_: reflexive-transitive closures
-- and bridges to/from the existing ⟶βη.
--
-- This file is the LANGUAGE foundation for the Di Cosmo factorisation
-- proof (Theory.Syntax.StrongCCL.CCT1.ConfluenceFullViaDiCosmo,
-- forthcoming). The four Lemma 2.7 obligations
--   WN R₁, NFClosed R₁ R₂, ConfOnNF R₁ R₂, R₁R₂-Commute R₁ R₂
-- live in their own focused modules.
--
-- ZERO POSTULATES.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.RuleSplit where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.CongruenceClosure

------------------------------------------------------------------------
-- R₁ rules : β ∪ s
------------------------------------------------------------------------

data _⟶R₁-rules_ : ∀ {A B} → Term A B → Term A B → Set where
  β-rule : ∀ {A B} {f g : Term A B} → f ⟶β g → f ⟶R₁-rules g
  s-rule : ∀ {A B} {f g : Term A B} → f ⟶s g → f ⟶R₁-rules g

infix 4 _⟶R₁-rules_

------------------------------------------------------------------------
-- R₂ rules : η
------------------------------------------------------------------------

data _⟶R₂-rules_ : ∀ {A B} → Term A B → Term A B → Set where
  η-rule : ∀ {A B} {f g : Term A B} → f ⟶η-CCT1 g → f ⟶R₂-rules g

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
-- Reflexive-transitive closures.
------------------------------------------------------------------------

data _⟶R₁*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶R₁* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶R₁ u → u ⟶R₁* v → t ⟶R₁* v

infix 4 _⟶R₁*_

data _⟶R₂*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶R₂* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶R₂ u → u ⟶R₂* v → t ⟶R₂* v

infix 4 _⟶R₂*_

⟶R₁*-trans : ∀ {A B} {t u v : Term A B} → t ⟶R₁* u → u ⟶R₁* v → t ⟶R₁* v
⟶R₁*-trans done       yz = yz
⟶R₁*-trans (r ∷ rs)   yz = r ∷ ⟶R₁*-trans rs yz

⟶R₂*-trans : ∀ {A B} {t u v : Term A B} → t ⟶R₂* u → u ⟶R₂* v → t ⟶R₂* v
⟶R₂*-trans done       yz = yz
⟶R₂*-trans (r ∷ rs)   yz = r ∷ ⟶R₂*-trans rs yz

------------------------------------------------------------------------
-- Bridge: ⟶R₁ ⊆ ⟶βη.
------------------------------------------------------------------------

R₁-rules-to-βη-rules : ∀ {A B} {f g : Term A B} →
                       f ⟶R₁-rules g → f ⟶βη-rules g
R₁-rules-to-βη-rules (β-rule r) = β-rule r
R₁-rules-to-βη-rules (s-rule r) = s-rule r

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
R₂-rules-to-βη-rules (η-rule r) = η-rule r

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
-- Each rule belongs to exactly one component:
--   β-rule, s-rule  →  ⟶R₁
--   η-rule          →  ⟶R₂
-- Congruences propagate via the ⊎ on the inner step.
------------------------------------------------------------------------

⟶βη-to-R₁⊎R₂ : ∀ {A B} {t u : Term A B} →
                t ⟶βη u → (t ⟶R₁ u) ⊎ (t ⟶R₂ u)
⟶βη-to-R₁⊎R₂ (βη-Closure.base (β-rule r)) =
  inj₁ (R₁-Closure.base (β-rule r))
⟶βη-to-R₁⊎R₂ (βη-Closure.base (s-rule r)) =
  inj₁ (R₁-Closure.base (s-rule r))
⟶βη-to-R₁⊎R₂ (βη-Closure.base (η-rule r)) =
  inj₂ (R₂-Closure.base (η-rule r))
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

------------------------------------------------------------------------
-- Bridge: ⟶R₁* ⊆ ⟶βη*  and  ⟶R₂* ⊆ ⟶βη*.
------------------------------------------------------------------------

⟶R₁*-to-⟶βη* : ∀ {A B} {t u : Term A B} → t ⟶R₁* u → t ⟶βη* u
⟶R₁*-to-⟶βη* done     = done
⟶R₁*-to-⟶βη* (r ∷ rs) = ⟶R₁-to-⟶βη r ∷ ⟶R₁*-to-⟶βη* rs

⟶R₂*-to-⟶βη* : ∀ {A B} {t u : Term A B} → t ⟶R₂* u → t ⟶βη* u
⟶R₂*-to-⟶βη* done     = done
⟶R₂*-to-⟶βη* (r ∷ rs) = ⟶R₂-to-⟶βη r ∷ ⟶R₂*-to-⟶βη* rs
