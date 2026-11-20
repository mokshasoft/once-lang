-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Generic.Parser — plan 0.153 D1: the generic type-grammar parser,
-- well-founded on `Acc _<_ (length toks)`, with no `with`, no `rewrite` and no
-- TERMINATING. Each parser's result carries its shrink (`<` for atom, prod,
-- sum, type; `≤` for the tails), which is what lets the next call take a
-- smaller `Acc`. Classifiers are consumed by top-level helpers that take the
-- classifier's RESULT as a parameter (D0); a classifier's consequence (the
-- tails' strict decrease) is passed as a function of that result.
------------------------------------------------------------------------

module Once.Parser.Generic.Parser where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
import Data.String as Str
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl; <-trans; <⇒≤; n<1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Grade using (Many)
open import Once.Parser.Token
open import Once.Parser.Generic.Relation

------------------------------------------------------------------------
-- Results that carry their shrink, and the maps between them.
------------------------------------------------------------------------

Res< : Set → ℕ → Set
Res< A n = Maybe (Σ[ a ∈ A ] Σ[ rest ∈ List Token ] length rest < n)

Res≤ : Set → ℕ → Set
Res≤ A n = Maybe (Σ[ a ∈ A ] Σ[ rest ∈ List Token ] length rest ≤ n)

forget< : ∀ {A n} → Res< A n → Maybe (A × List Token)
forget< (just (a , rest , _)) = just (a , rest)
forget< nothing               = nothing

forget≤ : ∀ {A n} → Res≤ A n → Maybe (A × List Token)
forget≤ (just (a , rest , _)) = just (a , rest)
forget≤ nothing               = nothing

-- a result on a strictly shorter suffix, read from the longer input
under : ∀ {A m n} → m < n → Res< A m → Res< A n
under p (just (a , rest , q)) = just (a , rest , <-trans q p)
under p nothing               = nothing

-- a tail's result after a strict prefix
after< : ∀ {A m n} → m < n → Res≤ A m → Res< A n
after< p (just (a , rest , q)) = just (a , rest , Data.Nat.Properties.≤-<-trans q p)
after< p nothing               = nothing

weaken : ∀ {A n} → Res< A n → Res≤ A n
weaken (just (a , rest , q)) = just (a , rest , <⇒≤ q)
weaken nothing               = nothing

mapRes : ∀ {A B n} → (A → B) → Res< A n → Res< B n
mapRes f (just (a , rest , q)) = just (f a , rest , q)
mapRes f nothing               = nothing

AccT : List Token → Set
AccT toks = Acc _<_ (length toks)

<3 : ∀ n → n < suc (suc (suc n))
<3 n = <-trans (n<1+n n) (<-trans (n<1+n _) (n<1+n _))

------------------------------------------------------------------------
-- Keyword views (D0: a view per question, its catch-all carries the value).
------------------------------------------------------------------------

data KwV : String → Set where
  vUnit  : KwV "Unit"
  vVoid  : KwV "Void"
  vInt   : KwV "Int"
  vFloat : KwV "Float"
  vEff   : KwV "Eff"
  vAct   : KwV "Act"
  vMu    : KwV "Mu"
  vNu    : KwV "Nu"
  vNone  : (s : String) → KwV s

kwD : (k : String) → KwV k → (s : String) → KwV s → Dec (s ≡ k) → KwV s
kwD k v .k other (yes refl) = v
kwD k v s  other (no _)     = other

kw : (k : String) → KwV k → (s : String) → KwV s → KwV s
kw k v s other = kwD k v s other (s Str.≟ k)

kwV : (s : String) → KwV s
kwV s = kw "Unit" vUnit s (kw "Void" vVoid s (kw "Int" vInt s (kw "Float" vFloat s
          (kw "Eff" vEff s (kw "Act" vAct s (kw "Mu" vMu s (kw "Nu" vNu s (vNone s))))))))

data FKwV : String → Set where
  fvId   : FKwV "Id"
  fvK    : FKwV "K"
  fvNone : (s : String) → FKwV s

fkwD : (k : String) → FKwV k → (s : String) → FKwV s → Dec (s ≡ k) → FKwV s
fkwD k v .k other (yes refl) = v
fkwD k v s  other (no _)     = other

fkwV : (s : String) → FKwV s
fkwV s = fkwD "Id" fvId s (fkwD "K" fvK s (fvNone s) (s Str.≟ "K")) (s Str.≟ "Id")

-- D313/D318: does the stream start `( Act`?
actD : (w : String) (r : List Token) → Dec (w ≡ "Act")
     → Maybe (Σ[ r′ ∈ List Token ] TLParen ∷ TWord w ∷ r ≡ TLParen ∷ TWord "Act" ∷ r′)
actD .("Act") r (yes refl) = just (r , refl)
actD w        r (no _)     = nothing

actHead? : (rest : List Token) → Maybe (Σ[ r ∈ List Token ] rest ≡ TLParen ∷ TWord "Act" ∷ r)
actHead? (TLParen ∷ TWord w ∷ r) = actD w r (w Str.≟ "Act")
{-# CATCHALL #-}
actHead? _ = nothing

-- The head token, and the closing parenthesis: a view each (D0), so that a
-- proof refutes "anything else" from a view variable, not by enumerating tokens.
data HeadV : List Token → Set where
  hWord  : ∀ name rest → HeadV (TWord name ∷ rest)
  hParen : ∀ rest → HeadV (TLParen ∷ rest)
  hOther : ∀ toks → HeadV toks

headV : (toks : List Token) → HeadV toks
headV (TWord name ∷ rest) = hWord name rest
headV (TLParen ∷ rest)    = hParen rest
{-# CATCHALL #-}
headV toks = hOther toks

data CloseV : List Token → Set where
  cR     : ∀ r2 → CloseV (TRParen ∷ r2)
  cOther : ∀ r → CloseV r

closeV : (r : List Token) → CloseV r
closeV (TRParen ∷ r2) = cR r2
{-# CATCHALL #-}
closeV r = cOther r

------------------------------------------------------------------------
-- The parser.
------------------------------------------------------------------------

module Make (alg : TyAlg) where
  open TyAlg alg

  -- `Nu ( Act F )`'s close: no recursion.
  nuC : ∀ r F r1 → length r1 < length r → CloseV r1 → Res< R (length (TWord "Nu" ∷ TLParen ∷ TWord "Act" ∷ r))
  nuC r F .(TRParen ∷ r2) p (cR r2)     = just (aNuAct F , r2 , <-trans (<-trans (n<1+n _) p) (<3 _))
  nuC r F r1              p (cOther .r1) = nothing

  nuClose : ∀ r → Res< RF (length r) → Res< R (length (TWord "Nu" ∷ TLParen ∷ TWord "Act" ∷ r))
  nuClose r (just (F , r1 , p)) = nuC r F r1 p (closeV r1)
  nuClose r nothing             = nothing

  parenC : ∀ {A} rest (T : A) r → length r < length rest → CloseV r → Res< A (length (TLParen ∷ rest))
  parenC rest T .(TRParen ∷ r2) p (cR r2)     = just (T , r2 , <-trans (n<1+n _) (<-trans p (n<1+n _)))
  parenC rest T r               p (cOther .r) = nothing

  parenK : ∀ {A} rest → Res< A (length rest) → Res< A (length (TLParen ∷ rest))
  parenK rest (just (T , r , p)) = parenC rest T r p (closeV r)
  parenK rest nothing            = nothing

  arrK : (R → R) → (toks t : List Token) → length t < length toks → Res< R (length t) → Res≤ R (length toks)
  arrK f toks t d (just (B , r , p)) = just (f B , r , <⇒≤ (<-trans p d))
  arrK f toks t d nothing            = nothing

  mutual
    atomA : ∀ toks → AccT toks → Res< R (length toks)
    atomA toks a = atomX toks a (extraP toks)

    atomX : ∀ toks → AccT toks → Maybe (Σ[ x ∈ R ] Σ[ r ∈ List Token ] Extra toks x r) → Res< R (length toks)
    atomX toks a (just (x , r , ex)) = just (x , r , extraShrink ex)
    atomX toks a nothing             = atomKw toks a

    atomKw : ∀ toks → AccT toks → Res< R (length toks)
    atomKw toks a = atomH toks (headV toks) a

    atomH : ∀ toks → HeadV toks → AccT toks → Res< R (length toks)
    atomH .(TWord name ∷ rest) (hWord name rest) a         = kwK name rest (kwV name) a
    atomH .(TLParen ∷ rest)    (hParen rest)     (acc rec) = parenK rest (typeA rest (rec (n<1+n _)))
    atomH toks                 (hOther .toks)    a         = nothing

    kwK : ∀ name rest → KwV name → AccT (TWord name ∷ rest) → Res< R (length (TWord name ∷ rest))
    kwK .("Unit")  rest vUnit  a = just (aUnit , rest , n<1+n _)
    kwK .("Void")  rest vVoid  a = just (aVoid , rest , n<1+n _)
    kwK .("Int")   rest vInt   a = just (aInt , rest , n<1+n _)
    kwK .("Float") rest vFloat a = just (aFloat , rest , n<1+n _)
    kwK .("Eff")   rest vEff   (acc rec) = twoK aEff "Eff" rest (atomA rest (rec (n<1+n _))) (acc rec)
    kwK .("Act")   rest vAct   (acc rec) = twoK aAct "Act" rest (atomA rest (rec (n<1+n _))) (acc rec)
    kwK .("Mu")    rest vMu    (acc rec) = under (n<1+n _) (mapRes aMu (fSumA rest (rec (n<1+n _))))
    kwK .("Nu")    rest vNu    (acc rec) = nuTry rest (acc rec) (fSumA rest (rec (n<1+n _)))
    kwK name       rest (vNone .name) a  = nothing

    -- `Eff A B`, `Act A B`: two atoms
    twoK : (R → R → R) → ∀ name rest → Res< R (length rest) → AccT (TWord name ∷ rest) → Res< R (length (TWord name ∷ rest))
    twoK f name rest (just (A , r1 , p)) (acc rec) =
      under (<-trans p (n<1+n _)) (mapRes (f A) (atomA r1 (rec (<-trans p (n<1+n _)))))
    twoK f name rest nothing a = nothing

    nuTry : ∀ rest → AccT (TWord "Nu" ∷ rest) → Res< RF (length rest) → Res< R (length (TWord "Nu" ∷ rest))
    nuTry rest a (just (F , r1 , p)) = just (aNu F , r1 , <-trans p (n<1+n _))
    nuTry rest a nothing             = nuAct rest a (actHead? rest)

    nuAct : ∀ rest → AccT (TWord "Nu" ∷ rest) → Maybe (Σ[ r ∈ List Token ] rest ≡ TLParen ∷ TWord "Act" ∷ r)
          → Res< R (length (TWord "Nu" ∷ rest))
    nuAct rest a nothing = nothing
    nuAct .(TLParen ∷ TWord "Act" ∷ r) (acc rec) (just (r , refl)) = nuClose r (fSumA r (rec (<3 _)))

    prodA : ∀ toks → AccT toks → Res< R (length toks)
    prodA toks a = prodK toks (atomA toks a) a

    prodK : ∀ toks → Res< R (length toks) → AccT toks → Res< R (length toks)
    prodK toks (just (A , r1 , p)) (acc rec) = after< p (prodTailA A r1 (rec p))
    prodK toks nothing a = nothing

    prodTailA : R → ∀ toks → AccT toks → Res≤ R (length toks)
    prodTailA l toks a = ptGo l toks (isStar toks) (isStar-< toks) a

    ptGo : R → ∀ toks (b : Bool) → (b ≡ true → length (drop1 toks) < length toks) → AccT toks → Res≤ R (length toks)
    ptGo l toks false bnd a         = just (l , toks , ≤-refl)
    ptGo l toks true  bnd (acc rec) = ptK l toks (bnd refl) (atomA (drop1 toks) (rec (bnd refl))) (acc rec)

    ptK : R → ∀ toks → length (drop1 toks) < length toks → Res< R (length (drop1 toks)) → AccT toks → Res≤ R (length toks)
    ptK l toks d (just (B , r2 , p)) (acc rec) =
      weaken (after< (<-trans p d) (prodTailA (aProd l B) r2 (rec (<-trans p d))))
    ptK l toks d nothing a = nothing

    sumA : ∀ toks → AccT toks → Res< R (length toks)
    sumA toks a = sumK toks (prodA toks a) a

    sumK : ∀ toks → Res< R (length toks) → AccT toks → Res< R (length toks)
    sumK toks (just (A , r1 , p)) (acc rec) = after< p (sumTailA A r1 (rec p))
    sumK toks nothing a = nothing

    sumTailA : R → ∀ toks → AccT toks → Res≤ R (length toks)
    sumTailA l toks a = stGo l toks (isPlus toks) (isPlus-< toks) a

    stGo : R → ∀ toks (b : Bool) → (b ≡ true → length (drop1 toks) < length toks) → AccT toks → Res≤ R (length toks)
    stGo l toks false bnd a         = just (l , toks , ≤-refl)
    stGo l toks true  bnd (acc rec) = stK l toks (bnd refl) (prodA (drop1 toks) (rec (bnd refl))) (acc rec)

    stK : R → ∀ toks → length (drop1 toks) < length toks → Res< R (length (drop1 toks)) → AccT toks → Res≤ R (length toks)
    stK l toks d (just (B , r2 , p)) (acc rec) =
      weaken (after< (<-trans p d) (sumTailA (aSum l B) r2 (rec (<-trans p d))))
    stK l toks d nothing a = nothing

    typeA : ∀ toks → AccT toks → Res< R (length toks)
    typeA toks a = typeK toks (sumA toks a) a

    typeK : ∀ toks → Res< R (length toks) → AccT toks → Res< R (length toks)
    typeK toks (just (A , r1 , p)) (acc rec) = after< p (arrowTailA A r1 (rec p))
    typeK toks nothing a = nothing

    arrowTailA : R → ∀ toks → AccT toks → Res≤ R (length toks)
    arrowTailA l toks a = atGo l toks (arrowDir toks) (arrowDir-A-< toks) (arrowDir-G-< toks) a

    atGo : R → ∀ toks (d : ArrowDir) → (d ≡ adA → length (drop1 toks) < length toks)
         → (∀ {q} → d ≡ adG q → length (drop2 toks) < length toks) → AccT toks → Res≤ R (length toks)
    atGo l toks adD     bA bG a         = just (l , toks , ≤-refl)
    atGo l toks adR     bA bG a         = nothing
    atGo l toks adA     bA bG (acc rec) = arrK (aArrow Many l) toks (drop1 toks) (bA refl) (typeA (drop1 toks) (rec (bA refl)))
    atGo l toks (adG q) bA bG (acc rec) = arrK (aArrow q l) toks (drop2 toks) (bG refl) (typeA (drop2 toks) (rec (bG refl)))

    fAtomA : ∀ toks → AccT toks → Res< RF (length toks)
    fAtomA toks a = fAtomH toks (headV toks) a

    fAtomH : ∀ toks → HeadV toks → AccT toks → Res< RF (length toks)
    fAtomH .(TWord name ∷ rest) (hWord name rest) a         = fkwK name rest (fkwV name) a
    fAtomH .(TLParen ∷ rest)    (hParen rest)     (acc rec) = parenK rest (fSumA rest (rec (n<1+n _)))
    fAtomH toks                 (hOther .toks)    a         = nothing

    fkwK : ∀ name rest → FKwV name → AccT (TWord name ∷ rest) → Res< RF (length (TWord name ∷ rest))
    fkwK .("Id") rest fvId a         = just (fId , rest , n<1+n _)
    fkwK .("K")  rest fvK  (acc rec) = under (n<1+n _) (mapRes fK (atomA rest (rec (n<1+n _))))
    fkwK name    rest (fvNone .name) a = nothing

    fProdA : ∀ toks → AccT toks → Res< RF (length toks)
    fProdA toks a = fProdK toks (fAtomA toks a) a

    fProdK : ∀ toks → Res< RF (length toks) → AccT toks → Res< RF (length toks)
    fProdK toks (just (A , r1 , p)) (acc rec) = after< p (fProdTailA A r1 (rec p))
    fProdK toks nothing a = nothing

    fProdTailA : RF → ∀ toks → AccT toks → Res≤ RF (length toks)
    fProdTailA l toks a = fptGo l toks (isStar toks) (isStar-< toks) a

    fptGo : RF → ∀ toks (b : Bool) → (b ≡ true → length (drop1 toks) < length toks) → AccT toks → Res≤ RF (length toks)
    fptGo l toks false bnd a         = just (l , toks , ≤-refl)
    fptGo l toks true  bnd (acc rec) = fptK l toks (bnd refl) (fAtomA (drop1 toks) (rec (bnd refl))) (acc rec)

    fptK : RF → ∀ toks → length (drop1 toks) < length toks → Res< RF (length (drop1 toks)) → AccT toks → Res≤ RF (length toks)
    fptK l toks d (just (B , r2 , p)) (acc rec) =
      weaken (after< (<-trans p d) (fProdTailA (fProd l B) r2 (rec (<-trans p d))))
    fptK l toks d nothing a = nothing

    fSumA : ∀ toks → AccT toks → Res< RF (length toks)
    fSumA toks a = fSumK toks (fProdA toks a) a

    fSumK : ∀ toks → Res< RF (length toks) → AccT toks → Res< RF (length toks)
    fSumK toks (just (A , r1 , p)) (acc rec) = after< p (fSumTailA A r1 (rec p))
    fSumK toks nothing a = nothing

    fSumTailA : RF → ∀ toks → AccT toks → Res≤ RF (length toks)
    fSumTailA l toks a = fstGo l toks (isPlus toks) (isPlus-< toks) a

    fstGo : RF → ∀ toks (b : Bool) → (b ≡ true → length (drop1 toks) < length toks) → AccT toks → Res≤ RF (length toks)
    fstGo l toks false bnd a         = just (l , toks , ≤-refl)
    fstGo l toks true  bnd (acc rec) = fstK l toks (bnd refl) (fProdA (drop1 toks) (rec (bnd refl))) (acc rec)

    fstK : RF → ∀ toks → length (drop1 toks) < length toks → Res< RF (length (drop1 toks)) → AccT toks → Res≤ RF (length toks)
    fstK l toks d (just (B , r2 , p)) (acc rec) =
      weaken (after< (<-trans p d) (fSumTailA (fSum l B) r2 (rec (<-trans p d))))
    fstK l toks d nothing a = nothing

  ----------------------------------------------------------------------
  -- The public, bound-free parsers: the same names and types as today's.
  ----------------------------------------------------------------------

  atomP prodP sumP typeP : List Token → Maybe (R × List Token)
  atomP toks = forget< (atomA toks (<-wellFounded _))
  prodP toks = forget< (prodA toks (<-wellFounded _))
  sumP  toks = forget< (sumA toks (<-wellFounded _))
  typeP toks = forget< (typeA toks (<-wellFounded _))

  prodTailP sumTailP arrowTailP : R → List Token → Maybe (R × List Token)
  prodTailP  l toks = forget≤ (prodTailA l toks (<-wellFounded _))
  sumTailP   l toks = forget≤ (sumTailA l toks (<-wellFounded _))
  arrowTailP l toks = forget≤ (arrowTailA l toks (<-wellFounded _))

  fAtomP fProdP fSumP : List Token → Maybe (RF × List Token)
  fAtomP toks = forget< (fAtomA toks (<-wellFounded _))
  fProdP toks = forget< (fProdA toks (<-wellFounded _))
  fSumP  toks = forget< (fSumA toks (<-wellFounded _))

  fProdTailP fSumTailP : RF → List Token → Maybe (RF × List Token)
  fProdTailP l toks = forget≤ (fProdTailA l toks (<-wellFounded _))
  fSumTailP  l toks = forget≤ (fSumTailA l toks (<-wellFounded _))
