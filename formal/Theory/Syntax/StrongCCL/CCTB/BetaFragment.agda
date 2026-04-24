------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCTB.BetaFragment
--
-- The β-fragment of Hardin1989's reduction: the congruence closure
-- of the 5 β-rules (fst-pair, snd-pair, eta-pair, id-left, id-right)
-- considered in isolation from the structural rules.
--
-- Rationale: while Hardin1989 as a whole uses the full βη+structural
-- system (confluent via Newman), the β-fragment alone is Church-Rosser
-- via Takahashi's parallel-reduction + diamond method. The proof lives
-- next to this module in BetaFragment/{ParallelReduction, Diamond,
-- Triangle, Confluence}.
--
-- Historical note: this β-fragment is essentially Curien's 1985
-- original CCL — the β-only system whose confluence Takahashi proved.
-- It is NOT by itself a valid CCC presentation (it doesn't equate
-- associativity, pair-distribution, or generalized η-pairing), which
-- is why Hardin 1989 added the structural rules. As a standalone
-- *rewrite system* it still has respectable meta-theoretic properties,
-- and this module collects them.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCTB.BetaFragment where

open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Re-export the carrier and β-rule constructors from Hardin1989.
------------------------------------------------------------------------

open import Theory.Syntax.StrongCCL.CCTB public
  using ( Ty; Unit; _×_
        ; Term; id; _∘_; terminal; fst; snd; ⟨_,_⟩
        ; _⟶β_; fst-pair; snd-pair; eta-pair; id-left; id-right)

------------------------------------------------------------------------
-- β-only reduction = congruence closure of the 5 β-rules.
------------------------------------------------------------------------

open import Theory.Syntax.CongruenceClosure
open CCTB-Close Ty _×_ Term _∘_ ⟨_,_⟩ _⟶β_ public
  renaming (Closed to _⟶_)

infix 4 _⟶_

data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

infix 4 _⟶*_

IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶ u)
