------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCTB.BetaFragment.Confluence
--
-- CCTB confluence: the _⟶*_ relation on CCTB terms is Church-Rosser.
--
-- Proof path:
--   1. Parallel reduction _⟹_ has diamond property
--      (via triangle lemma: t ⟹ u → u ⟹ t*).
--   2. Therefore Star _⟹_ is confluent (ConfluenceFromDiamond).
--   3. Bridges _⟶*_ ↔ Star _⟹_ transfer confluence.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCTB.BetaFragment.Confluence where

open import Theory.Syntax.StrongCCL.CCTB.BetaFragment
open import Theory.Syntax.StrongCCL.CCTB.BetaFragment.ParallelReduction
open import Theory.Syntax.StrongCCL.CCTB.BetaFragment.Diamond
open import Theory.Syntax.StrongCCL.CCTB.BetaFragment.Triangle
import Theory.Derived.ConfluenceFromDiamond as CFD
open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Diamond of parallel reduction (via triangle)
------------------------------------------------------------------------

⟹-diamond : ∀ {A B} → CFD.Diamond (_⟹_ {A} {B})
⟹-diamond {A} {B} {t} t⟹u t⟹v = (t * , triangle t⟹u , triangle t⟹v)

------------------------------------------------------------------------
-- Star _⟹_ is confluent (generic machinery)
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
-- CCTB confluence: the main result
------------------------------------------------------------------------

cctb-confluence : ∀ {A B} {t u v : Term A B} →
                  t ⟶* u → t ⟶* v →
                  Σ (Term A B) (λ w → (u ⟶* w) ∧ (v ⟶* w))
cctb-confluence tu tv with ⟹-confluent (⟶*-to-Star-⟹ tu) (⟶*-to-Star-⟹ tv)
... | (w , star-uw , star-vw) = (w , Star-⟹-to-⟶* star-uw , Star-⟹-to-⟶* star-vw)
