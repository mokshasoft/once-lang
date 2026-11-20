-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Generic.Complete — plan 0.153 D1: completeness of the Acc parser,
-- for EVERY `Acc` (so an induction hypothesis meets whatever `Acc` the
-- definition passes). No `with`, no `rewrite`: each step is a lemma about a
-- helper whose classifier result is a VARIABLE, matched `refl`, then applied
-- to the classifier (D0). Plan 0.7-2's wall (`rewrite` of `isStar toks` under
-- a bound that mentions it) cannot arise: nothing is abstracted.
------------------------------------------------------------------------

module Once.Parser.Generic.Complete where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_)
import Data.List
import Data.Nat
import Data.Nat.Properties
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.Spec.Grade using (Many)
open import Once.Parser.Token
open import Once.Parser.Generic.Relation
open import Once.Parser.Generic.Parser hiding (module Make)
import Once.Parser.Generic.Parser

------------------------------------------------------------------------
-- The maps forget the shrink.
------------------------------------------------------------------------

forget-under : ∀ {A m n} (p : _) (r : Res< A m) → forget< {n = n} (under p r) ≡ forget< r
forget-under p (just _) = refl
forget-under p nothing  = refl

forget-after : ∀ {A m n} (p : _) (r : Res≤ A m) → forget< {n = n} (after< p r) ≡ forget≤ r
forget-after p (just _) = refl
forget-after p nothing  = refl

forget-weaken : ∀ {A n} (r : Res< A n) → forget≤ (weaken r) ≡ forget< r
forget-weaken (just _) = refl
forget-weaken nothing  = refl

map-just : ∀ {A B n} (f : A → B) (r : Res< A n) {a rest} → forget< r ≡ just (a , rest)
         → forget< (mapRes f r) ≡ just (f a , rest)
map-just f (just _) refl = refl

module Make (alg : TyAlg) where
  open TyAlg alg
  open Gen alg
  open Once.Parser.Generic.Parser.Make alg

  ----------------------------------------------------------------------
  -- One lemma per helper, its dispatched value a variable.
  ----------------------------------------------------------------------

  atomX-miss : ∀ toks a m → m ≡ nothing → forget< (atomX toks a m) ≡ forget< (atomKw toks a)
  atomX-miss toks a .nothing refl = refl

  atomX-hit : ∀ toks a m {x r} (ex : Extra toks x r) → m ≡ just (x , r , ex) → forget< (atomX toks a m) ≡ just (x , r)
  atomX-hit toks a .(just (_ , _ , ex)) ex refl = refl

  parenK-ok : ∀ {A} rest (m : Res< A _) {T r2} → forget< m ≡ just (T , TRParen ∷ r2)
            → forget< (parenK rest m) ≡ just (T , r2)
  parenK-ok rest (just (T , TRParen ∷ r2 , p)) refl = refl

  twoK-ok : ∀ f name rest m a {A r1 B r2} → forget< m ≡ just (A , r1)
          → (∀ c → forget< (atomA r1 c) ≡ just (B , r2))
          → forget< (twoK f name rest m a) ≡ just (f A B , r2)
  twoK-ok f name rest (just (A , r1 , p)) (acc rec) refl hB = trans (forget-under _ _) (map-just (f A) _ (hB _))

  nuTry-just : ∀ rest a m {F r} → forget< m ≡ just (F , r) → forget< (nuTry rest a m) ≡ just (aNu F , r)
  nuTry-just rest a (just (F , r , p)) refl = refl

  nuTry-nothing : ∀ rest a m → m ≡ nothing → nuTry rest a m ≡ nuAct rest a (actHead? rest)
  nuTry-nothing rest a .nothing refl = refl

  nuClose-ok : ∀ r m {F r2} → forget< m ≡ just (F , TRParen ∷ r2) → forget< (nuClose r m) ≡ just (aNuAct F , r2)
  nuClose-ok r (just (F , TRParen ∷ r2 , p)) refl = refl

  -- D313: the functor parser rejects `( Act …`.
  fSum-parenAct : ∀ toks a → fSumA (TLParen ∷ TWord "Act" ∷ toks) a ≡ nothing
  fSum-parenAct toks (acc rec) = refl

  prodK-ok : ∀ toks m a {A r1 T rest} → forget< m ≡ just (A , r1)
           → (∀ c → forget≤ (prodTailA A r1 c) ≡ just (T , rest)) → forget< (prodK toks m a) ≡ just (T , rest)
  prodK-ok toks (just (A , r1 , p)) (acc rec) refl h = trans (forget-after p _) (h _)

  ptGo-done : ∀ l toks b bnd a → b ≡ false → forget≤ (ptGo l toks b bnd a) ≡ just (l , toks)
  ptGo-done l toks .false bnd a refl = refl

  ptK-ok : ∀ l toks d m a {B toks2 T rest} → forget< m ≡ just (B , toks2)
         → (∀ c → forget≤ (prodTailA (aProd l B) toks2 c) ≡ just (T , rest)) → forget≤ (ptK l toks d m a) ≡ just (T , rest)
  ptK-ok l toks d (just (B , r2 , p)) (acc rec) refl h = trans (forget-weaken _) (trans (forget-after _ _) (h _))

  ptGo-star : ∀ l toks b bnd a {B toks2 T rest} → b ≡ true
            → (∀ c → forget< (atomA (drop1 toks) c) ≡ just (B , toks2))
            → (∀ c → forget≤ (prodTailA (aProd l B) toks2 c) ≡ just (T , rest))
            → forget≤ (ptGo l toks b bnd a) ≡ just (T , rest)
  ptGo-star l toks .true bnd (acc rec) refl hB hT = ptK-ok l toks (bnd refl) _ (acc rec) (hB _) hT

  sumK-ok : ∀ toks m a {A r1 T rest} → forget< m ≡ just (A , r1)
          → (∀ c → forget≤ (sumTailA A r1 c) ≡ just (T , rest)) → forget< (sumK toks m a) ≡ just (T , rest)
  sumK-ok toks (just (A , r1 , p)) (acc rec) refl h = trans (forget-after p _) (h _)

  stGo-done : ∀ l toks b bnd a → b ≡ false → forget≤ (stGo l toks b bnd a) ≡ just (l , toks)
  stGo-done l toks .false bnd a refl = refl

  stK-ok : ∀ l toks d m a {B toks2 T rest} → forget< m ≡ just (B , toks2)
         → (∀ c → forget≤ (sumTailA (aSum l B) toks2 c) ≡ just (T , rest)) → forget≤ (stK l toks d m a) ≡ just (T , rest)
  stK-ok l toks d (just (B , r2 , p)) (acc rec) refl h = trans (forget-weaken _) (trans (forget-after _ _) (h _))

  stGo-plus : ∀ l toks b bnd a {B toks2 T rest} → b ≡ true
            → (∀ c → forget< (prodA (drop1 toks) c) ≡ just (B , toks2))
            → (∀ c → forget≤ (sumTailA (aSum l B) toks2 c) ≡ just (T , rest))
            → forget≤ (stGo l toks b bnd a) ≡ just (T , rest)
  stGo-plus l toks .true bnd (acc rec) refl hB hT = stK-ok l toks (bnd refl) _ (acc rec) (hB _) hT

  typeK-ok : ∀ toks m a {A r1 T rest} → forget< m ≡ just (A , r1)
           → (∀ c → forget≤ (arrowTailA A r1 c) ≡ just (T , rest)) → forget< (typeK toks m a) ≡ just (T , rest)
  typeK-ok toks (just (A , r1 , p)) (acc rec) refl h = trans (forget-after p _) (h _)

  arrK-ok : ∀ f toks t d m {B r} → forget< m ≡ just (B , r) → forget≤ (arrK f toks t d m) ≡ just (f B , r)
  arrK-ok f toks t d (just (B , r , p)) refl = refl

  atGo-done : ∀ l toks d bA (bG : ∀ {q} → d ≡ adG q → Data.List.length (drop2 toks) Data.Nat.< Data.List.length toks) a → d ≡ adD → forget≤ (atGo l toks d bA bG a) ≡ just (l , toks)
  atGo-done l toks .adD bA bG a refl = refl

  atGo-A : ∀ l toks d bA (bG : ∀ {q} → d ≡ adG q → Data.List.length (drop2 toks) Data.Nat.< Data.List.length toks) a {B rest} → d ≡ adA
         → (∀ c → forget< (typeA (drop1 toks) c) ≡ just (B , rest))
         → forget≤ (atGo l toks d bA bG a) ≡ just (aArrow Many l B , rest)
  atGo-A l toks .adA bA bG (acc rec) refl h = arrK-ok (aArrow Many l) toks (drop1 toks) _ _ (h _)

  atGo-G : ∀ l toks d bA (bG : ∀ {q} → d ≡ adG q → Data.List.length (drop2 toks) Data.Nat.< Data.List.length toks) a {q B rest} → d ≡ adG q
         → (∀ c → forget< (typeA (drop2 toks) c) ≡ just (B , rest))
         → forget≤ (atGo l toks d bA bG a) ≡ just (aArrow q l B , rest)
  atGo-G l toks .(adG _) bA bG (acc rec) refl h = arrK-ok (aArrow _ l) toks (drop2 toks) _ _ (h _)

  fProdK-ok : ∀ toks m a {A r1 T rest} → forget< m ≡ just (A , r1)
            → (∀ c → forget≤ (fProdTailA A r1 c) ≡ just (T , rest)) → forget< (fProdK toks m a) ≡ just (T , rest)
  fProdK-ok toks (just (A , r1 , p)) (acc rec) refl h = trans (forget-after p _) (h _)

  fptGo-done : ∀ l toks b bnd a → b ≡ false → forget≤ (fptGo l toks b bnd a) ≡ just (l , toks)
  fptGo-done l toks .false bnd a refl = refl

  fptK-ok : ∀ l toks d m a {B toks2 T rest} → forget< m ≡ just (B , toks2)
          → (∀ c → forget≤ (fProdTailA (fProd l B) toks2 c) ≡ just (T , rest)) → forget≤ (fptK l toks d m a) ≡ just (T , rest)
  fptK-ok l toks d (just (B , r2 , p)) (acc rec) refl h = trans (forget-weaken _) (trans (forget-after _ _) (h _))

  fptGo-star : ∀ l toks b bnd a {B toks2 T rest} → b ≡ true
             → (∀ c → forget< (fAtomA (drop1 toks) c) ≡ just (B , toks2))
             → (∀ c → forget≤ (fProdTailA (fProd l B) toks2 c) ≡ just (T , rest))
             → forget≤ (fptGo l toks b bnd a) ≡ just (T , rest)
  fptGo-star l toks .true bnd (acc rec) refl hB hT = fptK-ok l toks (bnd refl) _ (acc rec) (hB _) hT

  fSumK-ok : ∀ toks m a {A r1 T rest} → forget< m ≡ just (A , r1)
           → (∀ c → forget≤ (fSumTailA A r1 c) ≡ just (T , rest)) → forget< (fSumK toks m a) ≡ just (T , rest)
  fSumK-ok toks (just (A , r1 , p)) (acc rec) refl h = trans (forget-after p _) (h _)

  fstGo-done : ∀ l toks b bnd a → b ≡ false → forget≤ (fstGo l toks b bnd a) ≡ just (l , toks)
  fstGo-done l toks .false bnd a refl = refl

  fstK-ok : ∀ l toks d m a {B toks2 T rest} → forget< m ≡ just (B , toks2)
          → (∀ c → forget≤ (fSumTailA (fSum l B) toks2 c) ≡ just (T , rest)) → forget≤ (fstK l toks d m a) ≡ just (T , rest)
  fstK-ok l toks d (just (B , r2 , p)) (acc rec) refl h = trans (forget-weaken _) (trans (forget-after _ _) (h _))

  fstGo-plus : ∀ l toks b bnd a {B toks2 T rest} → b ≡ true
             → (∀ c → forget< (fProdA (drop1 toks) c) ≡ just (B , toks2))
             → (∀ c → forget≤ (fSumTailA (fSum l B) toks2 c) ≡ just (T , rest))
             → forget≤ (fstGo l toks b bnd a) ≡ just (T , rest)
  fstGo-plus l toks .true bnd (acc rec) refl hB hT = fstK-ok l toks (bnd refl) _ (acc rec) (hB _) hT

  ----------------------------------------------------------------------
  -- Completeness, for every Acc, by induction on the relation.
  ----------------------------------------------------------------------

  mutual
    complete-atomA : ∀ {toks T rest} → ParsesAtomG toks T rest → ∀ a → forget< (atomA toks a) ≡ just (T , rest)
    complete-atomA (pa-unit rest)  a = atomX-miss _ a _ (extraMiss-Unit rest)
    complete-atomA (pa-void rest)  a = atomX-miss _ a _ (extraMiss-Void rest)
    complete-atomA (pa-int rest)   a = atomX-miss _ a _ (extraMiss-Int rest)
    complete-atomA (pa-float rest) a = atomX-miss _ a _ (extraMiss-Float rest)
    complete-atomA (pa-eff {toks1} dA dB) (acc rec) =
      trans (atomX-miss _ (acc rec) _ (extraMiss-Eff toks1))
            (twoK-ok aEff "Eff" toks1 _ (acc rec) (complete-atomA dA _) (complete-atomA dB))
    complete-atomA (pa-act {toks1} dA dB) (acc rec) =
      trans (atomX-miss _ (acc rec) _ (extraMiss-Act toks1))
            (twoK-ok aAct "Act" toks1 _ (acc rec) (complete-atomA dA _) (complete-atomA dB))
    complete-atomA (pa-mu {toks} dF) (acc rec) =
      trans (atomX-miss _ (acc rec) _ (extraMiss-Mu toks))
            (trans (forget-under _ _) (map-just aMu _ (complete-fSumA dF _)))
    complete-atomA (pa-nu {toks} dF) (acc rec) =
      trans (atomX-miss _ (acc rec) _ (extraMiss-Nu toks)) (nuTry-just toks (acc rec) _ (complete-fSumA dF _))
    complete-atomA (pa-nu-act {toks} dF) (acc rec) =
      trans (atomX-miss _ (acc rec) _ (extraMiss-Nu (TLParen ∷ TWord "Act" ∷ toks)))
            (trans (Relation.Binary.PropositionalEquality.cong forget<
                     (nuTry-nothing _ (acc rec) _ (fSum-parenAct toks (rec (Data.Nat.Properties.n<1+n _)))))
                   (nuClose-ok toks _ (complete-fSumA dF _)))
    complete-atomA (pa-extra ex) a = atomX-hit _ a _ ex (extraComplete ex)
    complete-atomA (pa-paren {toks} dT refl) (acc rec) =
      trans (atomX-miss _ (acc rec) _ (extraMiss-LParen toks)) (parenK-ok toks _ (complete-typeA dT _))

    complete-prodA : ∀ {toks T rest} → ParsesProdG toks T rest → ∀ a → forget< (prodA toks a) ≡ just (T , rest)
    complete-prodA (pp-mk dA dT) a = prodK-ok _ _ a (complete-atomA dA a) (complete-prodTailA dT)

    complete-prodTailA : ∀ {l toks T rest} → ParsesProdTailG l toks T rest → ∀ a
                      → forget≤ (prodTailA l toks a) ≡ just (T , rest)
    complete-prodTailA (ppt-done eq) a = ptGo-done _ _ _ _ a eq
    complete-prodTailA (ppt-star eq dB dT) a = ptGo-star _ _ _ _ a eq (complete-atomA dB) (complete-prodTailA dT)

    complete-sumA : ∀ {toks T rest} → ParsesSumG toks T rest → ∀ a → forget< (sumA toks a) ≡ just (T , rest)
    complete-sumA (ps-mk dA dT) a = sumK-ok _ _ a (complete-prodA dA a) (complete-sumTailA dT)

    complete-sumTailA : ∀ {l toks T rest} → ParsesSumTailG l toks T rest → ∀ a
                     → forget≤ (sumTailA l toks a) ≡ just (T , rest)
    complete-sumTailA (pst-done eq) a = stGo-done _ _ _ _ a eq
    complete-sumTailA (pst-plus eq dB dT) a = stGo-plus _ _ _ _ a eq (complete-prodA dB) (complete-sumTailA dT)

    complete-typeA : ∀ {toks T rest} → ParsesTypeG toks T rest → ∀ a → forget< (typeA toks a) ≡ just (T , rest)
    complete-typeA (pt-mk dS dA) a = typeK-ok _ _ a (complete-sumA dS a) (complete-arrowTailA dA)

    complete-arrowTailA : ∀ {l toks T rest} → ParsesArrowTailG l toks T rest → ∀ a
                       → forget≤ (arrowTailA l toks a) ≡ just (T , rest)
    complete-arrowTailA (pat-done eq) a = atGo-done _ _ _ _ _ a eq
    complete-arrowTailA (pat-arrow eq dT) a = atGo-A _ _ _ _ _ a eq (complete-typeA dT)
    complete-arrowTailA (pat-arrow-g eq dT) a = atGo-G _ _ _ _ _ a eq (complete-typeA dT)

    complete-fAtomA : ∀ {toks F rest} → ParsesFuncAtomG toks F rest → ∀ a → forget< (fAtomA toks a) ≡ just (F , rest)
    complete-fAtomA (pfa-id rest) a = refl
    complete-fAtomA (pfa-k dA) (acc rec) = trans (forget-under _ _) (map-just fK _ (complete-atomA dA _))
    complete-fAtomA (pfa-paren {toks} dF refl) (acc rec) = parenK-ok toks _ (complete-fSumA dF _)

    complete-fProdA : ∀ {toks F rest} → ParsesFuncProdG toks F rest → ∀ a → forget< (fProdA toks a) ≡ just (F , rest)
    complete-fProdA (pfp-mk dA dT) a = fProdK-ok _ _ a (complete-fAtomA dA a) (complete-fProdTailA dT)

    complete-fProdTailA : ∀ {l toks F rest} → ParsesFuncProdTailG l toks F rest → ∀ a
                       → forget≤ (fProdTailA l toks a) ≡ just (F , rest)
    complete-fProdTailA (pfpt-done eq) a = fptGo-done _ _ _ _ a eq
    complete-fProdTailA (pfpt-star eq dB dT) a = fptGo-star _ _ _ _ a eq (complete-fAtomA dB) (complete-fProdTailA dT)

    complete-fSumA : ∀ {toks F rest} → ParsesFuncSumG toks F rest → ∀ a → forget< (fSumA toks a) ≡ just (F , rest)
    complete-fSumA (pfs-mk dA dT) a = fSumK-ok _ _ a (complete-fProdA dA a) (complete-fSumTailA dT)

    complete-fSumTailA : ∀ {l toks F rest} → ParsesFuncSumTailG l toks F rest → ∀ a
                      → forget≤ (fSumTailA l toks a) ≡ just (F , rest)
    complete-fSumTailA (pfst-done eq) a = fstGo-done _ _ _ _ a eq
    complete-fSumTailA (pfst-plus eq dB dT) a = fstGo-plus _ _ _ _ a eq (complete-fProdA dB) (complete-fSumTailA dT)

  ----------------------------------------------------------------------
  -- The public statements, today's names and types, over the bound-free parsers.
  ----------------------------------------------------------------------

  complete-atom : ∀ {toks T rest} → ParsesAtomG toks T rest → atomP toks ≡ just (T , rest)
  complete-atom d = complete-atomA d (<-wellFounded _)

  complete-prod : ∀ {toks T rest} → ParsesProdG toks T rest → prodP toks ≡ just (T , rest)
  complete-prod d = complete-prodA d (<-wellFounded _)

  complete-prodTail : ∀ {l toks T rest} → ParsesProdTailG l toks T rest → prodTailP l toks ≡ just (T , rest)
  complete-prodTail d = complete-prodTailA d (<-wellFounded _)

  complete-sum : ∀ {toks T rest} → ParsesSumG toks T rest → sumP toks ≡ just (T , rest)
  complete-sum d = complete-sumA d (<-wellFounded _)

  complete-sumTail : ∀ {l toks T rest} → ParsesSumTailG l toks T rest → sumTailP l toks ≡ just (T , rest)
  complete-sumTail d = complete-sumTailA d (<-wellFounded _)

  complete-type : ∀ {toks T rest} → ParsesTypeG toks T rest → typeP toks ≡ just (T , rest)
  complete-type d = complete-typeA d (<-wellFounded _)

  complete-arrowTail : ∀ {l toks T rest} → ParsesArrowTailG l toks T rest → arrowTailP l toks ≡ just (T , rest)
  complete-arrowTail d = complete-arrowTailA d (<-wellFounded _)

  complete-fAtom : ∀ {toks F rest} → ParsesFuncAtomG toks F rest → fAtomP toks ≡ just (F , rest)
  complete-fAtom d = complete-fAtomA d (<-wellFounded _)

  complete-fProd : ∀ {toks F rest} → ParsesFuncProdG toks F rest → fProdP toks ≡ just (F , rest)
  complete-fProd d = complete-fProdA d (<-wellFounded _)

  complete-fProdTail : ∀ {l toks F rest} → ParsesFuncProdTailG l toks F rest → fProdTailP l toks ≡ just (F , rest)
  complete-fProdTail d = complete-fProdTailA d (<-wellFounded _)

  complete-fSum : ∀ {toks F rest} → ParsesFuncSumG toks F rest → fSumP toks ≡ just (F , rest)
  complete-fSum d = complete-fSumA d (<-wellFounded _)

  complete-fSumTail : ∀ {l toks F rest} → ParsesFuncSumTailG l toks F rest → fSumTailP l toks ≡ just (F , rest)
  complete-fSumTail d = complete-fSumTailA d (<-wellFounded _)
