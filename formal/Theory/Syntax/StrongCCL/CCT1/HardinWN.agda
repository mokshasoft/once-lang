------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.HardinWN
--
-- Weak normalisation of Hardin's R₁.
--
-- SN R₁ : DISCHARGED via Acc-monotonicity from Tait sn.
-- WN R₁ : postulated. Standard derivation from SN R₁ + decidable
--         R₁-redex existence (mechanical, ~150 lines deferred).
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.HardinWN where

open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.StrongCCL.CCT1.HardinSplit
  using (_⟶R₁_; ⟶R₁-to-⟶βη)
open import Theory.Syntax.StrongCCL.CCT1.Tait using (sn)
open import Theory.Derived.Newman using (Acc; acc)
open import Theory.Derived.ConfluenceFromDiamond
  using (Star) renaming (done to star-done; _∷_ to _star∷_)

------------------------------------------------------------------------
-- SN R₁ : free from Tait sn via Acc-monotonicity.
------------------------------------------------------------------------

acc-monotone : ∀ {A : Set} {R S : A → A → Set} →
               (∀ {x y} → R x y → S x y) →
               ∀ {x} → Acc S x → Acc R x
acc-monotone RS (acc h) = acc λ rxy → acc-monotone RS (h (RS rxy))

sn-R₁ : ∀ {A B} (t : Term A B) → Acc (_⟶R₁_ {A} {B}) t
sn-R₁ {A} {B} t = acc-monotone (⟶R₁-to-⟶βη {A} {B}) (sn t)

------------------------------------------------------------------------
-- IsNF predicate.
------------------------------------------------------------------------

IsNF-R₁ : ∀ {A B} → Term A B → Set
IsNF-R₁ {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶R₁ u)

------------------------------------------------------------------------
-- WN R₁ : POSTULATED pending decidability of R₁-redex existence.
------------------------------------------------------------------------

postulate
  wn-R₁ : ∀ {A B} (t : Term A B) →
          Σ (Term A B) (λ nf → Star (_⟶R₁_ {A} {B}) t nf ∧ IsNF-R₁ nf)
