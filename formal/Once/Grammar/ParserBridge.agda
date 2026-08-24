-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.ParserBridge
--
-- Bridges the inductive parsing relations (`ParsesX`, defined in
-- `ParserRelation`) with the WF-based parser functions in
-- `Once.Parser.Type`:
--
--   * `complete-X` : `ParsesX toks T rest → parseX toks ≡ just (T, rest)`
--     — the function produces a result consistent with any derivation.
--   * `sound-X`    : `parseX toks ≡ just (T, rest) → ParsesX toks T rest`
--     — the function's output comes from a genuine derivation.
--
-- Completeness is what Roundtrip needs (given structural derivation,
-- conclude parser returns the expected result). Soundness is what
-- ParserInvariant needs (given parser output, extract a derivation
-- from which NoMuNu is a structural induction).
--
-- Both directions' compound cases use `Acc-irrelevant` to convert
-- between arbitrary WF Acc values. This is the one place the Acc-
-- threading friction lives; downstream proofs never mention Acc.
------------------------------------------------------------------------

module Once.Grammar.ParserBridge where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃; ∃-syntax)
open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <⇒≤;
                                        n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Once.Type using (Type; Unit; _*_; _+_; _⇒[_]_;
                             Quantity; Zero; One; Many;
                             Functor; K; Id; _⊕_; _⊗_; μ-type)
open import Once.Parser.Token
open import Once.Parser.Type
open import Once.Parser.AccIrrelevant using (Acc-irrelevant)
open import Once.Grammar.ParserRelation

------------------------------------------------------------------------
-- Irrelevance of Acc for each WF parser
------------------------------------------------------------------------

parseTypeAtomWF-irr :
  ∀ (toks : List Token) (a b : Acc _<_ (length toks))
  → parseTypeAtomWF toks a ≡ parseTypeAtomWF toks b
parseTypeAtomWF-irr toks a b =
  cong (parseTypeAtomWF toks) (Acc-irrelevant a b)

parseTypeWF-irr :
  ∀ (toks : List Token) (a b : Acc _<_ (length toks))
  → parseTypeWF toks a ≡ parseTypeWF toks b
parseTypeWF-irr toks a b =
  cong (parseTypeWF toks) (Acc-irrelevant a b)

parseTypeSumWF-irr :
  ∀ (toks : List Token) (a b : Acc _<_ (length toks))
  → parseTypeSumWF toks a ≡ parseTypeSumWF toks b
parseTypeSumWF-irr toks a b =
  cong (parseTypeSumWF toks) (Acc-irrelevant a b)

parseTypeProdWF-irr :
  ∀ (toks : List Token) (a b : Acc _<_ (length toks))
  → parseTypeProdWF toks a ≡ parseTypeProdWF toks b
parseTypeProdWF-irr toks a b =
  cong (parseTypeProdWF toks) (Acc-irrelevant a b)

parseTypeProdTailWF-irr :
  ∀ (t : Type) (toks : List Token) (a b : Acc _<_ (length toks))
  → parseTypeProdTailWF t toks a ≡ parseTypeProdTailWF t toks b
parseTypeProdTailWF-irr t toks a b =
  cong (parseTypeProdTailWF t toks) (Acc-irrelevant a b)

parseTypeSumTailWF-irr :
  ∀ (t : Type) (toks : List Token) (a b : Acc _<_ (length toks))
  → parseTypeSumTailWF t toks a ≡ parseTypeSumTailWF t toks b
parseTypeSumTailWF-irr t toks a b =
  cong (parseTypeSumTailWF t toks) (Acc-irrelevant a b)

parseArrowTailWF-irr :
  ∀ (t : Type) (toks : List Token) (a b : Acc _<_ (length toks))
  → parseArrowTailWF t toks a ≡ parseArrowTailWF t toks b
parseArrowTailWF-irr t toks a b =
  cong (parseArrowTailWF t toks) (Acc-irrelevant a b)

------------------------------------------------------------------------
-- Wrapper equations: `parseX toks ≡ stripBound< (parseXWF toks a)` for
-- any Acc `a`. Follows from the definition of the wrapper + Acc-irr.
------------------------------------------------------------------------

parseType-as-strippedWF :
  ∀ toks (a : Acc _<_ (length toks))
  → parseType toks ≡ stripType toks (parseTypeWF toks a)
parseType-as-strippedWF toks a =
  cong (stripType toks)
       (parseTypeWF-irr toks (<-wellFounded (length toks)) a)

parseTypeAtom-as-strippedWF :
  ∀ toks (a : Acc _<_ (length toks))
  → parseTypeAtom toks ≡ stripAtom toks (parseTypeAtomWF toks a)
parseTypeAtom-as-strippedWF toks a =
  cong (stripAtom toks)
       (parseTypeAtomWF-irr toks (<-wellFounded (length toks)) a)

parseTypeSum-as-strippedWF :
  ∀ toks (a : Acc _<_ (length toks))
  → parseTypeSum toks ≡ stripSum toks (parseTypeSumWF toks a)
parseTypeSum-as-strippedWF toks a =
  cong (stripSum toks)
       (parseTypeSumWF-irr toks (<-wellFounded (length toks)) a)

parseTypeProd-as-strippedWF :
  ∀ toks (a : Acc _<_ (length toks))
  → parseTypeProd toks ≡ stripProd toks (parseTypeProdWF toks a)
parseTypeProd-as-strippedWF toks a =
  cong (stripProd toks)
       (parseTypeProdWF-irr toks (<-wellFounded (length toks)) a)

parseTypeProdTail-as-strippedWF :
  ∀ t toks (a : Acc _<_ (length toks))
  → parseTypeProdTail t toks ≡ stripProdTail t toks (parseTypeProdTailWF t toks a)
parseTypeProdTail-as-strippedWF t toks a =
  cong (stripProdTail t toks)
       (parseTypeProdTailWF-irr t toks (<-wellFounded (length toks)) a)

parseTypeSumTail-as-strippedWF :
  ∀ t toks (a : Acc _<_ (length toks))
  → parseTypeSumTail t toks ≡ stripSumTail t toks (parseTypeSumTailWF t toks a)
parseTypeSumTail-as-strippedWF t toks a =
  cong (stripSumTail t toks)
       (parseTypeSumTailWF-irr t toks (<-wellFounded (length toks)) a)

parseArrowTail-as-strippedWF :
  ∀ t toks (a : Acc _<_ (length toks))
  → parseArrowTail t toks ≡ stripArrowTail t toks (parseArrowTailWF t toks a)
parseArrowTail-as-strippedWF t toks a =
  cong (stripArrowTail t toks)
       (parseArrowTailWF-irr t toks (<-wellFounded (length toks)) a)

------------------------------------------------------------------------
-- Completeness (raw form): a derivation of `ParsesX toks T rest` gives
-- the EXACT WF-parser return `just (T , rest , someBound)`. We return
-- the bound existentially because different Acc values may produce
-- different witnesses; the Σ hides that.
--
-- Stating completeness in RAW form (without stripBound<) is crucial:
-- downstream compound cases `rewrite` with IH results to replace the
-- nested `parseTypeAtomWF toks1 (rec ...)` expression inside the
-- parser's with-tree. The stripBound wrapper around the IH would
-- prevent the rewrite from matching (stripBound only appears at the
-- outer wrapper level).
------------------------------------------------------------------------

mutual

  complete-atomWFraw :
    ∀ {toks T rest} (d : ParsesAtom toks T rest) (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesAtom toks T rest)
    → parseTypeAtomWF toks a ≡ just (T , rest , d')

  complete-prodWFraw :
    ∀ {toks T rest} (d : ParsesProd toks T rest) (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesProd toks T rest)
    → parseTypeProdWF toks a ≡ just (T , rest , d')

  complete-prodTailWFraw :
    ∀ {left toks T rest} (d : ParsesProdTail left toks T rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesProdTail left toks T rest)
    → parseTypeProdTailWF left toks a ≡ just (T , rest , d')

  complete-sumWFraw :
    ∀ {toks T rest} (d : ParsesSum toks T rest) (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesSum toks T rest)
    → parseTypeSumWF toks a ≡ just (T , rest , d')

  complete-sumTailWFraw :
    ∀ {left toks T rest} (d : ParsesSumTail left toks T rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesSumTail left toks T rest)
    → parseTypeSumTailWF left toks a ≡ just (T , rest , d')

  complete-arrowTailWFraw :
    ∀ {left toks T rest} (d : ParsesArrowTail left toks T rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesArrowTail left toks T rest)
    → parseArrowTailWF left toks a ≡ just (T , rest , d')

  complete-typeWFraw :
    ∀ {toks T rest} (d : ParsesType toks T rest) (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesType toks T rest)
    → parseTypeWF toks a ≡ just (T , rest , d')

  complete-functorAtomWFraw :
    ∀ {toks F rest} (d : ParsesFunctorAtom toks F rest) (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesFunctorAtom toks F rest)
    → parseFunctorAtomWF toks a ≡ just (F , rest , d')

  complete-functorProdWFraw :
    ∀ {toks F rest} (d : ParsesFunctorProd toks F rest) (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesFunctorProd toks F rest)
    → parseFunctorProdWF toks a ≡ just (F , rest , d')

  complete-functorProdTailWFraw :
    ∀ {left toks F rest} (d : ParsesFunctorProdTail left toks F rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesFunctorProdTail left toks F rest)
    → parseFunctorProdTailWF left toks a ≡ just (F , rest , d')

  complete-functorSumWFraw :
    ∀ {toks F rest} (d : ParsesFunctorSum toks F rest) (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesFunctorSum toks F rest)
    → parseFunctorSumWF toks a ≡ just (F , rest , d')

  complete-functorSumTailWFraw :
    ∀ {left toks F rest} (d : ParsesFunctorSumTail left toks F rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesFunctorSumTail left toks F rest)
    → parseFunctorSumTailWF left toks a ≡ just (F , rest , d')

  -- Base atom cases
  complete-atomWFraw (pa-unit   rest) _ = _ , refl
  complete-atomWFraw (pa-void   rest) _ = _ , refl
  complete-atomWFraw (pa-int    rest) _ = _ , refl
  complete-atomWFraw (pa-float  rest) _ = _ , refl
  complete-atomWFraw (pa-buffer rest) _ = _ , refl
  complete-atomWFraw (pa-string rest) _ = _ , refl

  -- Eff A B: two recursive atom parses.
  complete-atomWFraw (pa-eff {toks1 = toks1} {toks2 = toks2} {rest}
                             dA dB) (acc rec)
    with complete-atomWFraw dA (rec (s≤s ≤-refl))
  ... | dA' , eqA
    rewrite eqA
    with complete-atomWFraw dB (rec (<-trans (ParsesAtom-shrinks dA') (s≤s ≤-refl)))
  ... | dB' , eqB
    rewrite eqB
    = _ , refl

  -- IO A: single recursive atom parse, desugar to Eff Unit A.
  complete-atomWFraw (pa-io {toks1 = toks1} {rest} dA) (acc rec)
    with complete-atomWFraw dA (rec (s≤s ≤-refl))
  ... | bA , eqA
    rewrite eqA
    = _ , refl

  -- ( type ): inner parseType recursion, outer expects TRParen.
  complete-atomWFraw (pa-paren {toks = toks0} {rest2 = rest2}
                               dT refl) (acc rec)
    with complete-typeWFraw dT (rec (s≤s ≤-refl))
  ... | bT , eqT
    rewrite eqT
    = _ , refl

  -- Mu F: functor-sum recursion.
  complete-atomWFraw (pa-mu dF) (acc rec)
    with complete-functorSumWFraw dF (rec (s≤s ≤-refl))
  ... | dF' , eqF
    rewrite eqF
    = _ , refl

  -- Product level
  complete-prodWFraw (pp-mk dA dTail) (acc rec)
    with complete-atomWFraw dA (acc rec)
  ... | dA' , eqA
    rewrite eqA
    with complete-prodTailWFraw dTail (rec (ParsesAtom-shrinks dA'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Product-tail done cases: NotStar toks witnesses the first token
  -- isn't TStar, so the parser takes the identity branch.
  complete-prodTailWFraw (ppt-done {toks = []} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TLParen    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TRParen    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TLBrace    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TRBrace    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TColon     ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TEquals    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TArrow     ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TCaret0    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TCaret1    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TCaretW    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TLambda    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TComma     ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TSemicolon ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TAt        ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TPipe      ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TDot       ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TPlus      ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TMinus     ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TSlash     ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TPercent   ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TAmpersand ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TLt        ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TLe        ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TGt        ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TGe        ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TEqEq      ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TNeq       ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TBang      ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TNewline   ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TEOF       ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TWord _    ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TInt _ _     ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TFloat _ _ _ _ ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TString _  ∷ _} _) _ = _ , refl
  complete-prodTailWFraw (ppt-done {toks = TStar ∷ _} ()) _

  -- ProdTail star: consume TStar + atom + recurse on prodTail.
  complete-prodTailWFraw (ppt-star dB dTail) (acc rec)
    with complete-atomWFraw dB (rec (s≤s ≤-refl))
  ... | dB' , eqB
    rewrite eqB
    with complete-prodTailWFraw dTail (rec (<-trans (ParsesAtom-shrinks dB') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Sum level (mirrors Product)
  complete-sumWFraw (ps-mk dA dTail) (acc rec)
    with complete-prodWFraw dA (acc rec)
  ... | dA' , eqA
    rewrite eqA
    with complete-sumTailWFraw dTail (rec (ParsesProd-shrinks dA'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Sum-tail done cases
  complete-sumTailWFraw (pst-done {toks = []} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TLParen    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TRParen    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TLBrace    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TRBrace    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TColon     ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TEquals    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TArrow     ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TCaret0    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TCaret1    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TCaretW    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TLambda    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TComma     ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TSemicolon ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TAt        ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TPipe      ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TDot       ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TMinus     ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TStar      ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TSlash     ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TPercent   ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TAmpersand ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TLt        ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TLe        ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TGt        ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TGe        ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TEqEq      ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TNeq       ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TBang      ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TNewline   ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TEOF       ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TWord _    ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TInt _ _     ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TFloat _ _ _ _ ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TString _  ∷ _} _) _ = _ , refl
  complete-sumTailWFraw (pst-done {toks = TPlus ∷ _} ()) _

  -- Sum-tail plus: consume TPlus + prod + recurse.
  complete-sumTailWFraw (pst-plus dB dTail) (acc rec)
    with complete-prodWFraw dB (rec (s≤s ≤-refl))
  ... | dB' , eqB
    rewrite eqB
    with complete-sumTailWFraw dTail (rec (<-trans (ParsesProd-shrinks dB') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Arrow-tail done cases
  complete-arrowTailWFraw (pat-done {toks = []} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TLParen    ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TRParen    ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TLBrace    ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TRBrace    ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TColon     ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TEquals    ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TLambda    ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TComma     ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TSemicolon ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TAt        ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TPipe      ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TDot       ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TMinus     ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TStar      ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TSlash     ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TPercent   ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TAmpersand ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TLt        ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TLe        ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TGt        ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TGe        ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TEqEq      ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TNeq       ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TBang      ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TNewline   ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TEOF       ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TWord _    ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TInt _ _     ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TFloat _ _ _ _ ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TString _  ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TPlus   ∷ _} _) _ = _ , refl
  complete-arrowTailWFraw (pat-done {toks = TArrow  ∷ _} ()) _
  complete-arrowTailWFraw (pat-done {toks = TCaret0 ∷ _} ()) _
  complete-arrowTailWFraw (pat-done {toks = TCaret1 ∷ _} ()) _
  complete-arrowTailWFraw (pat-done {toks = TCaretW ∷ _} ()) _

  -- Arrow-tail graded: TCaret* ∷ TArrow ∷ rest with recursive type.
  complete-arrowTailWFraw (pat-arrow-g {q = Zero} dT) (acc rec)
    with complete-typeWFraw dT (rec (s≤s (n≤1+n _)))
  ... | bT , eqT
    rewrite eqT
    = _ , refl
  complete-arrowTailWFraw (pat-arrow-g {q = One} dT) (acc rec)
    with complete-typeWFraw dT (rec (s≤s (n≤1+n _)))
  ... | bT , eqT
    rewrite eqT
    = _ , refl
  complete-arrowTailWFraw (pat-arrow-g {q = Many} dT) (acc rec)
    with complete-typeWFraw dT (rec (s≤s (n≤1+n _)))
  ... | bT , eqT
    rewrite eqT
    = _ , refl

  -- Arrow-tail plain (no grade, defaults to Many).
  complete-arrowTailWFraw (pat-arrow dT) (acc rec)
    with complete-typeWFraw dT (rec (s≤s ≤-refl))
  ... | bT , eqT
    rewrite eqT
    = _ , refl

  -- Type level = sum + arrow tail
  complete-typeWFraw (pt-mk dS dA) (acc rec)
    with complete-sumWFraw dS (acc rec)
  ... | dS' , eqS
    rewrite eqS
    with complete-arrowTailWFraw dA (rec (ParsesSum-shrinks dS'))
  ... | dA' , eqA
    rewrite eqA
    = _ , refl

  ----------------------------------------------------------------------
  -- Functor sub-grammar completeness (mirrors the type levels).
  ----------------------------------------------------------------------

  -- Functor atom: Id / K atom / ( fSum ).
  complete-functorAtomWFraw (pfa-id rest) _ = _ , refl
  complete-functorAtomWFraw (pfa-k dA) (acc rec)
    with complete-atomWFraw dA (rec (s≤s ≤-refl))
  ... | dA' , eqA
    rewrite eqA
    = _ , refl
  complete-functorAtomWFraw (pfa-paren dF refl) (acc rec)
    with complete-functorSumWFraw dF (rec (s≤s ≤-refl))
  ... | dF' , eqF
    rewrite eqF
    = _ , refl

  -- Functor product level.
  complete-functorProdWFraw (pfp-mk dA dTail) (acc rec)
    with complete-functorAtomWFraw dA (acc rec)
  ... | dA' , eqA
    rewrite eqA
    with complete-functorProdTailWFraw dTail (rec (ParsesFunctorAtom-shrinks dA'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Functor product-tail done cases (NotStar witnesses first token ≠ TStar).
  complete-functorProdTailWFraw (pfpt-done {toks = []} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TLParen    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TRParen    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TLBrace    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TRBrace    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TColon     ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TEquals    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TArrow     ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TCaret0    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TCaret1    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TCaretW    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TLambda    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TComma     ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TSemicolon ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TAt        ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TPipe      ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TDot       ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TPlus      ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TMinus     ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TSlash     ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TPercent   ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TAmpersand ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TLt        ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TLe        ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TGt        ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TGe        ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TEqEq      ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TNeq       ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TBang      ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TNewline   ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TEOF       ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TWord _    ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TInt _ _     ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TFloat _ _ _ _ ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TString _  ∷ _} _) _ = _ , refl
  complete-functorProdTailWFraw (pfpt-done {toks = TStar ∷ _} ()) _

  complete-functorProdTailWFraw (pfpt-star dB dTail) (acc rec)
    with complete-functorAtomWFraw dB (rec (s≤s ≤-refl))
  ... | dB' , eqB
    rewrite eqB
    with complete-functorProdTailWFraw dTail (rec (<-trans (ParsesFunctorAtom-shrinks dB') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Functor sum level.
  complete-functorSumWFraw (pfs-mk dA dTail) (acc rec)
    with complete-functorProdWFraw dA (acc rec)
  ... | dA' , eqA
    rewrite eqA
    with complete-functorSumTailWFraw dTail (rec (ParsesFunctorProd-shrinks dA'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Functor sum-tail done cases (NotStarPlus witnesses first token ≠ TPlus).
  complete-functorSumTailWFraw (pfst-done {toks = []} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TLParen    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TRParen    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TLBrace    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TRBrace    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TColon     ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TEquals    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TArrow     ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TCaret0    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TCaret1    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TCaretW    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TLambda    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TComma     ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TSemicolon ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TAt        ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TPipe      ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TDot       ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TMinus     ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TStar      ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TSlash     ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TPercent   ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TAmpersand ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TLt        ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TLe        ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TGt        ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TGe        ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TEqEq      ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TNeq       ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TBang      ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TNewline   ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TEOF       ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TWord _    ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TInt _ _     ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TFloat _ _ _ _ ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TString _  ∷ _} _) _ = _ , refl
  complete-functorSumTailWFraw (pfst-done {toks = TPlus ∷ _} ()) _

  complete-functorSumTailWFraw (pfst-plus dB dTail) (acc rec)
    with complete-functorProdWFraw dB (rec (s≤s ≤-refl))
  ... | dB' , eqB
    rewrite eqB
    with complete-functorSumTailWFraw dTail (rec (<-trans (ParsesFunctorProd-shrinks dB') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

------------------------------------------------------------------------
-- Wrapper-level completeness theorems
------------------------------------------------------------------------

complete-atom :
  ∀ {toks T rest} → ParsesAtom toks T rest
  → parseTypeAtom toks ≡ just (T , rest)
complete-atom {toks} d
  with complete-atomWFraw d (<-wellFounded (length toks))
... | b , eq = cong (stripAtom toks) eq

complete-type :
  ∀ {toks T rest} → ParsesType toks T rest
  → parseType toks ≡ just (T , rest)
complete-type {toks} d
  with complete-typeWFraw d (<-wellFounded (length toks))
... | b , eq = cong (stripType toks) eq

------------------------------------------------------------------------
-- Soundness: a successful parse produces a genuine derivation.
--
-- Structure mirrors completeness — case-split on the token list /
-- WF-parser clause, extract the derivation. Used by `ParserInvariant`
-- to lift NoMuNu from a structural induction on `ParsesX`.

-- With the Dec-valued parser, soundness is a trivial projection: the
-- parser's success case already carries the derivation in its
-- returned Σ.

-- Invert a `stripX` equation to expose the underlying Σ-value carrying
-- the derivation.
stripType-inv :
  ∀ toks (r : ParseTypeD toks) {T rest}
  → stripType toks r ≡ just (T , rest)
  → ∃ λ (d : ParsesType toks T rest) → r ≡ just (T , rest , d)
stripType-inv toks nothing ()
stripType-inv toks (just (t , r , d)) refl = d , refl

stripAtom-inv :
  ∀ toks (r : ParseAtomD toks) {T rest}
  → stripAtom toks r ≡ just (T , rest)
  → ∃ λ (d : ParsesAtom toks T rest) → r ≡ just (T , rest , d)
stripAtom-inv toks nothing ()
stripAtom-inv toks (just (t , r , d)) refl = d , refl

sound-type :
  ∀ {toks T rest} → parseType toks ≡ just (T , rest)
  → ParsesType toks T rest
sound-type {toks} eq
  with stripType-inv toks (parseTypeWF toks (<-wellFounded (length toks))) eq
... | d , _ = d

sound-atom :
  ∀ {toks T rest} → parseTypeAtom toks ≡ just (T , rest)
  → ParsesAtom toks T rest
sound-atom {toks} eq
  with stripAtom-inv toks (parseTypeAtomWF toks (<-wellFounded (length toks))) eq
... | d , _ = d
