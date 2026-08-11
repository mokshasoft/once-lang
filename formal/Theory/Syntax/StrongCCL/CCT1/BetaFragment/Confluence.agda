------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.BetaFragment.Confluence
--
-- β-CCT1 confluence, rigorously derived.
--
-- SCOPE: this proves confluence of the β-subset of CCT1 reduction
-- (β rules + eta-pair inherited from CCTB). curry-η is excluded from
-- the rule system used here — see BaseRules.agda for the βη-tangle
-- rationale. Full βη-CCT1 confluence is proved separately via
-- Newman's lemma; this file provides only the β-subset result.
--
-- Proof path:
--   1. Parallel reduction _⟹_ has diamond property via triangle.
--   2. Star _⟹_ is confluent (ConfluenceFromDiamond).
--   3. Bridges _⟶*_ ↔ Star _⟹_ transfer confluence.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.BetaFragment.Confluence where

open import Theory.Syntax.StrongCCL.CCT1.BetaFragment
open import Theory.Syntax.StrongCCL.CCT1.BetaFragment.ParallelReduction
open import Theory.Syntax.StrongCCL.CCT1.BetaFragment.Diamond
open import Theory.Syntax.StrongCCL.CCT1.BetaFragment.Triangle
import Theory.Derived.ConfluenceFromDiamond as CFD
open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Diamond of parallel reduction
------------------------------------------------------------------------

⟹-diamond : ∀ {A B} → CFD.Diamond (_⟹_ {A} {B})
⟹-diamond {A} {B} {t} t⟹u t⟹v = (t * , triangle t⟹u , triangle t⟹v)

------------------------------------------------------------------------
-- Star _⟹_ is confluent
------------------------------------------------------------------------

⟹-confluent : ∀ {A B} → CFD.Confluent (_⟹_ {A} {B})
⟹-confluent = CFD.confluence ⟹-diamond

------------------------------------------------------------------------
-- Bridges between _⟶*_ and Star _⟹_
------------------------------------------------------------------------

⟶*-to-Star-⟹ : ∀ {A B} {t u : Term A B} → t ⟶* u → CFD.Star (_⟹_ {A} {B}) t u
⟶*-to-Star-⟹ done     = CFD.done
⟶*-to-Star-⟹ (r ∷ rs) = ⟶-to-⟹ r CFD.∷ ⟶*-to-Star-⟹ rs

Star-⟹-to-⟶* : ∀ {A B} {t u : Term A B} → CFD.Star (_⟹_ {A} {B}) t u → t ⟶* u
Star-⟹-to-⟶* CFD.done       = done
Star-⟹-to-⟶* (r CFD.∷ rs)   = ⟶*-trans (⟹-to-⟶* r) (Star-⟹-to-⟶* rs)

------------------------------------------------------------------------
-- β-CCT1 confluence — the main result of this file
--
-- NOTE: this covers the β-subset only (curry-η excluded from _⟶_ here).
-- Full βη-CCT1 confluence is derived via Newman's lemma elsewhere.
------------------------------------------------------------------------

cct1-β-confluence : ∀ {A B} {t u v : Term A B} →
                    t ⟶* u → t ⟶* v →
                    Σ (Term A B) (λ w → (u ⟶* w) ∧ (v ⟶* w))
cct1-β-confluence tu tv with ⟹-confluent (⟶*-to-Star-⟹ tu) (⟶*-to-Star-⟹ tv)
... | (w , star-uw , star-vw) = (w , Star-⟹-to-⟶* star-uw , Star-⟹-to-⟶* star-vw)
