------------------------------------------------------------------------
-- normalizer.Theory.Eval.NormalizeFullCorrectness
--
-- CAPSTONE (non-degenerate): the conclusion of the full "fixpoint ⟹
-- correct on ALL inputs" theorem for the REAL normalizer with spec = nf.
--
--     normalize-correct-all :
--       ∀ g → (normalize ∘ encode g) ⇓ᵈ mkVal (eval (encode (nf g)))
--
-- This is literally `RanzowFixpoint.EvalFullCorrectness.Correct nf normalize`
-- (the abstract `Correct spec N = ∀ g. (N ∘ encode g) ⇓ encVal (spec g)`,
-- with N = normalize and encVal g = mkVal (eval (encode g))). Unlike
-- RefoldFullCorrectness (spec = id, BranchwiseCorrect = ⊤, degenerate), here
-- the normal form `nf g` genuinely id-eliminates, and the semantic content
-- is `Adequacy.adequacy` — the code-level normalizer on ⌜g⌝ produces the
-- code of ⌜nf g⌝.
--
-- Lifted from the value at `tt` via ⊤/function eta (the `cong (λ z → λ _ →
-- z)`, exactly as RefoldFullCorrectness); no funext. The only extra step is
-- `toStd`, transporting `adequacy`'s bootstrap-prelude `_≡_` to the stdlib
-- `_≡_` that the abstract `_⇓ᵈ_` is stated in (the two identity types are
-- isomorphic).
--
-- Postulate-free; NO confluence, NO strong normalization.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/NormalizeFullCorrectness.agda
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Theory.Eval.NormalizeFullCorrectness where

open import normalizer.Syntax.Types using (⊤; tt)
open import normalizer.Syntax.CCC using (Term; _∘_)
open import normalizer.Encoding.Encoding using (encode)
open import normalizer.Testing.Evaluator using (eval)
open import normalizer.TCB0.Normalizer.Handlers using (normalize)
open import normalizer.Theory.Eval.NfSpec using (nf)
open import normalizer.Theory.Eval.Adequacy using (adequacy)
open import normalizer.Theory.Eval.Instance using (mkVal; _⇓ᵈ_)

import normalizer.Syntax.Types as B            -- bootstrap-prelude _≡_
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)  -- stdlib _≡_

-- The two propositional-equality types are isomorphic; transport a proof.
toStd : ∀ {A : Set} {x y : A} → x B.≡ y → x ≡ y
toStd B.refl = refl

------------------------------------------------------------------------
-- Correct on ALL inputs, for spec = nf: the real normalizer on every
-- encoded input ⌜g⌝ evaluates to the value of ⌜nf g⌝. The semantic content
-- is `adequacy`; the `cong` lifts the value-at-tt equation to the ⊤-indexed
-- function compared by `_⇓ᵈ_`.
------------------------------------------------------------------------

normalize-correct-all :
  ∀ {A C} (g : Term A C) →
  (normalize ∘ encode g) ⇓ᵈ mkVal (eval (encode (nf g)))
normalize-correct-all g = cong (λ z → λ (_ : ⊤) → z) (toStd (adequacy g))
