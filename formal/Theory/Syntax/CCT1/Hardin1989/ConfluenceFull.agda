------------------------------------------------------------------------
-- Theory.Syntax.CCT1.ConfluenceFull
--
-- Full CCT1 confluence (categorically-complete 13-rule system):
--   CCTB: id-left, id-right, assoc, fst-pair, snd-pair, eta-pair,
--         eta-pair-gen, pair-dist, term-unique
--   CCT1: curry-β, curry-η, curry-compose, curry-apply
--
-- Derived from SN (Theory.Syntax.CCT1.Tait, via sn) and local
-- confluence (Theory.Syntax.CCT1.LocalConfluence) via Newman's lemma
-- (Theory.Derived.Newman).
--
-- Status: SN and LC each have a small number of internal postulates
-- (classical Tait / critical-pair work items). This module assembles
-- the final theorem from those ingredients.
------------------------------------------------------------------------

module Theory.Syntax.CCT1.Hardin1989.ConfluenceFull where

open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)

open import Theory.Syntax.CCT1.Hardin1989
open import Theory.Syntax.CCT1.Hardin1989.Tait            using (sn)
open import Theory.Syntax.CCT1.Hardin1989.LocalConfluence  using (local-confluent;
                                                        ⟶βη*-trans; single)
open import Theory.Derived.Newman
  using (Acc; acc; SN; LocalConfluent; Confluent; newman; star-acc)
open import Theory.Derived.ConfluenceFromDiamond
  using (Star) renaming (done to star-done; _∷_ to _star∷_)

------------------------------------------------------------------------
-- Bridge between _⟶βη*_ and generic Star _⟶βη_
------------------------------------------------------------------------

⟶βη*-to-Star : ∀ {A B} {t u : Term A B} →
               t ⟶βη* u → Star (_⟶βη_ {A} {B}) t u
⟶βη*-to-Star done     = star-done
⟶βη*-to-Star (r ∷ rs) = r star∷ (⟶βη*-to-Star rs)

Star-to-⟶βη* : ∀ {A B} {t u : Term A B} →
               Star (_⟶βη_ {A} {B}) t u → t ⟶βη* u
Star-to-⟶βη* star-done      = done
Star-to-⟶βη* (r star∷ rs)   = r ∷ Star-to-⟶βη* rs

------------------------------------------------------------------------
-- Lift our native LocalConfluent into Newman's form (which uses Star)
------------------------------------------------------------------------

lc-newman : ∀ {A B} → LocalConfluent (_⟶βη_ {A} {B})
lc-newman {A} {B} r₁ r₂ with local-confluent r₁ r₂
... | (w , t→w , u→w) =
  w , ⟶βη*-to-Star t→w , ⟶βη*-to-Star u→w

sn-all : ∀ {A B} → SN (_⟶βη_ {A} {B})
sn-all t = sn t

------------------------------------------------------------------------
-- Main theorem: CCT1 confluence.
------------------------------------------------------------------------

⟶βη-star-confluent : ∀ {A B} → Confluent (_⟶βη_ {A} {B})
⟶βη-star-confluent {A} {B} =
  newman {R = _⟶βη_ {A} {B}} lc-newman sn-all

cct1-confluence : ∀ {A B} {t u v : Term A B} →
                  t ⟶βη* u → t ⟶βη* v →
                  Σ (Term A B) (λ w → (u ⟶βη* w) ∧ (v ⟶βη* w))
cct1-confluence tu tv
  with ⟶βη-star-confluent (⟶βη*-to-Star tu) (⟶βη*-to-Star tv)
... | (w , star-uw , star-vw) =
  w , Star-to-⟶βη* star-uw , Star-to-⟶βη* star-vw
