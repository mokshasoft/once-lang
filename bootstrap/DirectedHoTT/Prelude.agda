------------------------------------------------------------------------
-- DirectedHoTT · THE PRELUDE — one metalanguage, and it is the stdlib's.
--
-- ★★★ WHY THIS EXISTS.  Until 2026-09-07 this tree took its `_≡_` from
--   `normalizer.Syntax.Types` — a hand-rolled prelude living in a PEER
--   POC.  Two consequences, both bad:
--
--   1. THE TREE HELD TWO `_≡_`s.  235 modules used the hand-rolled one;
--      `Metatheory/FormerCensus` and `Examples/Knot/Census` used
--      `Agda.Builtin.Equality`, because reflection needs it.  Those two
--      STRADDLED the split — they compiled only because they never stated
--      an equation relating the two worlds.  An induction with one half
--      in each does not go through, and that is not hypothetical: it is
--      the failure this module was created to end.
--   2. `LESSONS.md` §5 says the POC owns its syntax and must not depend
--      on the normalizer.  The dependency was on a stdlib SUBSTITUTE that
--      happens to live in a normalizer-named module — honoured in
--      substance, violated in letter, and impossible to check.
--
-- ⚠ THIS IS A RE-EXPORT, NOT A DEFINITION.  Nothing is declared here.
--   Every name below is the STANDARD LIBRARY's, so a lemma proved in
--   `Metatheory/` and a lemma proved with `Data.Nat.Properties` are about
--   the same `_≡_` and compose.  `bootstrap.agda-lib` already carried
--   `depend: … standard-library`, so this costs no new dependency.
--
-- ⚠ WHAT CHANGED SEMANTICALLY.  The two `_≡_`s are not the same
--   declaration:
--
--     hand-rolled  data _≡_ {A : Set} : A → A → Set        -- both INDICES
--     stdlib       data _≡_ {a} {A : Set a} (x : A) : A → Set a   -- x a PARAMETER
--
--   Pattern-match unification behaves differently at a parameter than at
--   an index, and the stdlib's is universe-polymorphic.  Both differences
--   are real; neither turned out to bite (see PLAN-INTEGRATION axis 0).
--
-- ⚠ `Σ`'s FIELDS ARE `proj₁`/`proj₂` HERE, not `fst`/`snd`.  The
--   hand-rolled record named them `fst`/`snd`, which also collided with
--   the `RTm` constructors of the same name.  134 projection sites were
--   rewritten; the collision is gone as a side effect.
--
-- ★ THE RULE THIS ENCODES: use the standard library wherever a
--   standardised name already exists.  Add a re-export here rather than
--   hand-rolling a local copy — `Lib/IWk`'s own `Maybe`/`⊥`,
--   `Spec/Variance`'s own `𝔹` and `Metatheory/Canonicity`'s own `_≤_` are
--   the debt this rule exists to stop growing.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Prelude where

open import Relation.Binary.PropositionalEquality public
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Data.Empty public
  using ( ⊥; ⊥-elim )
open import Data.Product public
  using ( Σ; _,_; _×_; proj₁; proj₂ )
open import Data.Sum public
  using ( _⊎_; inj₁; inj₂ )
open import Data.Unit public
  using ( ⊤; tt )
open import Relation.Nullary public
  using ( ¬_ )
