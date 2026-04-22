------------------------------------------------------------------------
-- Theory.Syntax.CCT1.Confluence
--
-- CCT1 confluence, rigorously derived (no postulates).
--
-- Proof path:
--   1. Parallel reduction _⟹_ has diamond property via triangle.
--   2. Star _⟹_ is confluent (ConfluenceFromDiamond).
--   3. Bridges _⟶*_ ↔ Star _⟹_ transfer confluence.
--
-- Scope: proves confluence of the β-only CCT1 reduction (includes
-- eta-pair from CCTB, whose syntactically-specific pattern causes
-- no βη-tangle). curry-η is excluded from the rule system for this
-- reason; see BaseRules.agda. Full βη-confluence is future work.
------------------------------------------------------------------------

module Theory.Syntax.CCT1.Confluence where

open import Theory.Syntax.CCT1
open import Theory.Syntax.CCT1.ParallelReduction
open import Theory.Syntax.CCT1.Diamond
open import Theory.Syntax.CCT1.Triangle
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
-- CCT1 confluence — the main result
------------------------------------------------------------------------

cct1-confluence : ∀ {A B} {t u v : Term A B} →
                  t ⟶* u → t ⟶* v →
                  Σ (Term A B) (λ w → (u ⟶* w) ∧ (v ⟶* w))
cct1-confluence tu tv with ⟹-confluent (⟶*-to-Star-⟹ tu) (⟶*-to-Star-⟹ tv)
... | (w , star-uw , star-vw) = (w , Star-⟹-to-⟶* star-uw , Star-⟹-to-⟶* star-vw)
