-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Generic.Complete — generic completeness: every derivation is
-- found by the bound-free generic parser. Inducts on the relation; each clause
-- `rewrite`s the classifier premise (+ the extra-hook facts) then the IHs. No
-- bound in the parser ⇒ no bound-dependency ⇒ the rewrites reduce. Plan 0.7-2.
------------------------------------------------------------------------

module Once.Parser.Generic.Complete where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Parser.Token
open import Once.Parser.Generic.Relation
import Once.Parser.Generic.Parser as P

module Make (alg : TyAlg) where
  open TyAlg alg
  open Gen alg
  open P.Make alg

  mutual
    complete-atom : ∀ {toks T rest} → ParsesAtomG toks T rest → atomP toks ≡ just (T , rest)
    complete-atom (pa-unit rest)   rewrite extraMiss-Unit rest   = refl
    complete-atom (pa-void rest)   rewrite extraMiss-Void rest   = refl
    complete-atom (pa-int rest)    rewrite extraMiss-Int rest    = refl
    complete-atom (pa-float rest)  rewrite extraMiss-Float rest  = refl
    complete-atom (pa-buffer rest) rewrite extraMiss-Buffer rest = refl
    complete-atom (pa-string rest) rewrite extraMiss-String rest = refl
    complete-atom (pa-eff {toks1} dA dB)
      rewrite extraMiss-Eff toks1 | complete-atom dA | complete-atom dB = refl
    complete-atom (pa-io {toks1} dA)
      rewrite extraMiss-IO toks1 | complete-atom dA = refl
    complete-atom (pa-mu {toks} dF)
      rewrite extraMiss-Mu toks | complete-fSum dF = refl
    complete-atom (pa-extra ex) rewrite extraComplete ex = refl
    complete-atom (pa-paren {toks} dT refl)
      rewrite extraMiss-LParen toks | complete-type dT = refl

    complete-prod : ∀ {toks T rest} → ParsesProdG toks T rest → prodP toks ≡ just (T , rest)
    complete-prod (pp-mk dA dT) rewrite complete-atom dA | complete-prodTail dT = refl

    complete-prodTail : ∀ {l toks T rest} → ParsesProdTailG l toks T rest → prodTailP l toks ≡ just (T , rest)
    complete-prodTail (ppt-done eq) rewrite eq = refl
    complete-prodTail (ppt-star eq dB dT) rewrite eq | complete-atom dB | complete-prodTail dT = refl

    complete-sum : ∀ {toks T rest} → ParsesSumG toks T rest → sumP toks ≡ just (T , rest)
    complete-sum (ps-mk dA dT) rewrite complete-prod dA | complete-sumTail dT = refl

    complete-sumTail : ∀ {l toks T rest} → ParsesSumTailG l toks T rest → sumTailP l toks ≡ just (T , rest)
    complete-sumTail (pst-done eq) rewrite eq = refl
    complete-sumTail (pst-plus eq dB dT) rewrite eq | complete-prod dB | complete-sumTail dT = refl

    complete-type : ∀ {toks T rest} → ParsesTypeG toks T rest → typeP toks ≡ just (T , rest)
    complete-type (pt-mk dS dA) rewrite complete-sum dS | complete-arrowTail dA = refl

    complete-arrowTail : ∀ {l toks T rest} → ParsesArrowTailG l toks T rest → arrowTailP l toks ≡ just (T , rest)
    complete-arrowTail (pat-done eq) rewrite eq = refl
    complete-arrowTail (pat-arrow eq dT) rewrite eq | complete-type dT = refl
    complete-arrowTail (pat-arrow-g eq dT) rewrite eq | complete-type dT = refl

    complete-fAtom : ∀ {toks F rest} → ParsesFuncAtomG toks F rest → fAtomP toks ≡ just (F , rest)
    complete-fAtom (pfa-id rest) = refl
    complete-fAtom (pfa-k dA) rewrite complete-atom dA = refl
    complete-fAtom (pfa-paren dF refl) rewrite complete-fSum dF = refl

    complete-fProd : ∀ {toks F rest} → ParsesFuncProdG toks F rest → fProdP toks ≡ just (F , rest)
    complete-fProd (pfp-mk dA dT) rewrite complete-fAtom dA | complete-fProdTail dT = refl

    complete-fProdTail : ∀ {l toks F rest} → ParsesFuncProdTailG l toks F rest → fProdTailP l toks ≡ just (F , rest)
    complete-fProdTail (pfpt-done eq) rewrite eq = refl
    complete-fProdTail (pfpt-star eq dB dT) rewrite eq | complete-fAtom dB | complete-fProdTail dT = refl

    complete-fSum : ∀ {toks F rest} → ParsesFuncSumG toks F rest → fSumP toks ≡ just (F , rest)
    complete-fSum (pfs-mk dA dT) rewrite complete-fProd dA | complete-fSumTail dT = refl

    complete-fSumTail : ∀ {l toks F rest} → ParsesFuncSumTailG l toks F rest → fSumTailP l toks ≡ just (F , rest)
    complete-fSumTail (pfst-done eq) rewrite eq = refl
    complete-fSumTail (pfst-plus eq dB dT) rewrite eq | complete-fProd dB | complete-fSumTail dT = refl
