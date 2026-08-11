------------------------------------------------------------------------
-- Theory.Syntax.CCTB.ConfluenceFull
--
-- Full CCTB confluence (the complete universal-property rule set):
--   fst-pair, snd-pair, eta-pair, id-left, id-right, assoc, pair-dist,
--   eta-pair-gen, term-unique
--
-- Derived from SN (Theory.Syntax.CCTB.SN) and local confluence
-- (Theory.Syntax.CCTB.LocalConfluence) via Newman's lemma
-- (Theory.Derived.Newman).
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCTB.ConfluenceFull where

open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)

open import Theory.Syntax.StrongCCL.CCTB
open import Theory.Syntax.StrongCCL.CCTB.SN              using (sn)
open import Theory.Syntax.StrongCCL.CCTB.LocalConfluence using (local-confluent;
                                                       ⟶full*-trans; single)
open import Theory.Derived.Newman
  using (Acc; acc; SN; LocalConfluent; Confluent; newman; star-acc)
open import Theory.Derived.ConfluenceFromDiamond
  using (Star) renaming (done to star-done; _∷_ to _star∷_)

------------------------------------------------------------------------
-- Bridge between _⟶full*_ and the generic Star _⟶full_
------------------------------------------------------------------------

⟶full*-to-Star : ∀ {A B} {t u : Term A B} →
                 t ⟶full* u → Star (_⟶full_ {A} {B}) t u
⟶full*-to-Star done     = star-done
⟶full*-to-Star (r ∷ rs) = r star∷ (⟶full*-to-Star rs)

Star-to-⟶full* : ∀ {A B} {t u : Term A B} →
                 Star (_⟶full_ {A} {B}) t u → t ⟶full* u
Star-to-⟶full* star-done      = done
Star-to-⟶full* (r star∷ rs)   = r ∷ Star-to-⟶full* rs

------------------------------------------------------------------------
-- Bridge for joinability: Newman's Joinable (via Star) ↔ our Joinable
-- (via _⟶full*_)
------------------------------------------------------------------------

-- Newman's LocalConfluent uses Star; ours uses _⟶full*_. Convert.
lc-newman : ∀ {A B} → LocalConfluent (_⟶full_ {A} {B})
lc-newman {A} {B} r₁ r₂ with local-confluent r₁ r₂
... | (w , t→w , u→w) =
  w , ⟶full*-to-Star t→w , ⟶full*-to-Star u→w

------------------------------------------------------------------------
-- Assemble confluence via Newman's lemma
------------------------------------------------------------------------

-- SN at every type, packaged to match Newman's SN (∀ x, Acc R x).
sn-all : ∀ {A B} → SN (_⟶full_ {A} {B})
sn-all {A} {B} t = sn t

-- Confluence of Star _⟶full_ via Newman.
--   Newman : SN R → LocalConfluent R → Confluent R
⟶full-star-confluent : ∀ {A B} → Confluent (_⟶full_ {A} {B})
⟶full-star-confluent {A} {B} =
  newman {R = _⟶full_ {A} {B}} lc-newman sn-all

------------------------------------------------------------------------
-- CCTB full confluence, in our native _⟶full*_ form.
------------------------------------------------------------------------

cctb-confluence : ∀ {A B} {t u v : Term A B} →
                  t ⟶full* u → t ⟶full* v →
                  Σ (Term A B) (λ w → (u ⟶full* w) ∧ (v ⟶full* w))
cctb-confluence tu tv
  with ⟶full-star-confluent (⟶full*-to-Star tu) (⟶full*-to-Star tv)
... | (w , star-uw , star-vw) =
  w , Star-to-⟶full* star-uw , Star-to-⟶full* star-vw
