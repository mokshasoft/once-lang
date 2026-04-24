------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.BetaFragment
--
-- The β-fragment of Hardin1989's CCT1 reduction: the congruence
-- closure of the 6 β-rules (the 5 CCTB β-rules plus curry-β)
-- considered in isolation from the η-rules and structural rules.
--
-- This fragment is Church-Rosser via Takahashi's parallel-reduction +
-- diamond method (see BetaFragment/{ParallelReduction, Diamond,
-- Triangle, Confluence}).
--
-- Historical note: this β-fragment is essentially Curien's 1985
-- original CCL at CCT1. It is NOT by itself a valid CCC presentation
-- — the structural laws and the curry η-laws don't hold purely under
-- β-reduction — but as a standalone *rewrite system* it has
-- respectable confluence properties, captured here.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.BetaFragment where

open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Re-export the carrier and β-rule machinery from Hardin1989.
------------------------------------------------------------------------

open import Theory.Syntax.StrongCCL.CCT1 public
  using ( Ty; Unit; _×_; _⇒_
        ; Term; id; _∘_; terminal; fst; snd; ⟨_,_⟩; curry; apply
        ; _⟶β_; from-CCTB; from-CCT1
        ; fst-pair; snd-pair; eta-pair; id-left; id-right
        ; curry-β)

------------------------------------------------------------------------
-- β-only reduction = CCT1 congruence closure of the 6 β-rules.
------------------------------------------------------------------------

open import Theory.Syntax.CongruenceClosure
open CCT1-Close Ty _×_ _⇒_ Term _∘_ ⟨_,_⟩ curry _⟶β_ public
  renaming (Closed to _⟶_)

infix 4 _⟶_

data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

infix 4 _⟶*_

IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶ u)
