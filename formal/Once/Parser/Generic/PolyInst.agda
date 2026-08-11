-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Generic.PolyInst — instantiate the generic type-grammar parser
-- at PolyType. The extra atom is a lowercase TVar. Yields ParsesPolyType (the
-- independent relation) + a bound-free parser + sound/complete, all derived
-- from the generic Make modules with zero new postulates. Plan 0.7-2.
------------------------------------------------------------------------

module Once.Parser.Generic.PolyInst where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Nat using (_<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)

open import Once.Type
  using ( PolyType; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; Pμ-type
        ; PInt; PFloat; PStr; PBuffer; PTVar
        ; PolyFunctor; PK; PId; _P⊕_; _P⊗_ )
open import Once.Parser.Token
open import Once.Parser.CharClass using (isLowerWord)
open import Once.Parser.Generic.Relation
import Once.Parser.Generic.Parser as P
import Once.Parser.Generic.Sound as S
import Once.Parser.Generic.Complete as C

------------------------------------------------------------------------
-- The extra atom: a lowercase TVar.
------------------------------------------------------------------------

data TVarRel : List Token → PolyType → List Token → Set where
  tvar : ∀ {name rest} → isLowerWord name ≡ true → TVarRel (TWord name ∷ rest) (PTVar name) rest

-- De-`with` through a top-level `tvarGo` taking the classifier Bool as a
-- parameter (`isLowerWord name` is stuck on the abstract `name`, so an inline
-- `with` cannot fire in proofs). Completeness then inducts on that Bool.
tvarGo : (name : String) (rest : List Token) (b : Bool) → b ≡ isLowerWord name →
         Maybe (Σ[ a ∈ PolyType ] Σ[ r ∈ List Token ] TVarRel (TWord name ∷ rest) a r)
tvarGo name rest true  pf = just (PTVar name , rest , tvar (sym pf))
tvarGo name rest false pf = nothing

tvarP : (toks : List Token) → Maybe (Σ[ a ∈ PolyType ] Σ[ rest ∈ List Token ] TVarRel toks a rest)
tvarP (TWord name ∷ rest) = tvarGo name rest (isLowerWord name) refl
tvarP []        = nothing
tvarP (_ ∷ _)   = nothing

tvar-shrink : ∀ {toks a rest} → TVarRel toks a rest → length rest < length toks
tvar-shrink (tvar _) = s≤s ≤-refl

tvarGo-complete : ∀ (name : String) (rest : List Token) (b : Bool) (pf : b ≡ isLowerWord name)
  (lw : isLowerWord name ≡ true) → tvarGo name rest b pf ≡ just (PTVar name , rest , tvar lw)
tvarGo-complete name rest true  pf lw = cong (λ p → just (PTVar name , rest , tvar p)) (uip (sym pf) lw)
tvarGo-complete name rest false pf lw with trans pf lw
... | ()

tvar-complete : ∀ {toks a rest} (ex : TVarRel toks a rest) → tvarP toks ≡ just (a , rest , ex)
tvar-complete (tvar {name} {rest} lw) = tvarGo-complete name rest (isLowerWord name) refl lw

------------------------------------------------------------------------
-- The algebra.
------------------------------------------------------------------------

PolyAlg : TyAlg
PolyAlg = record
  { R = PolyType ; RF = PolyFunctor
  ; aUnit = PUnit ; aVoid = PVoid ; aInt = PInt ; aFloat = PFloat
  ; aBuffer = PBuffer ; aStr = PStr
  ; aProd = _P*_ ; aSum = _P+_ ; aEff = PEff
  ; aArrow = λ q A B → A P⇒[ q ] B
  ; aMu = Pμ-type
  ; fK = PK ; fId = PId ; fSum = _P⊕_ ; fProd = _P⊗_
  ; Extra = TVarRel ; extraShrink = tvar-shrink ; extraP = tvarP
  ; extraComplete = tvar-complete
  ; extraMiss-Unit   = λ _ → refl ; extraMiss-Void  = λ _ → refl
  ; extraMiss-Int    = λ _ → refl ; extraMiss-Float = λ _ → refl
  ; extraMiss-Buffer = λ _ → refl ; extraMiss-String = λ _ → refl
  ; extraMiss-Eff    = λ _ → refl ; extraMiss-IO    = λ _ → refl
  ; extraMiss-Mu     = λ _ → refl ; extraMiss-LParen = λ _ → refl
  }

------------------------------------------------------------------------
-- Derived: relation, parser, sound, complete for PolyType.
------------------------------------------------------------------------

open Gen PolyAlg public
  renaming ( ParsesTypeG to ParsesPolyType
           ; typeShrink to ParsesPolyType-shrink )
open P.Make PolyAlg public renaming (typeP to parsePolyTypeP)
open S.Make PolyAlg public renaming (sound-type to sound-polyType)
open C.Make PolyAlg public renaming (complete-type to complete-polyType)
