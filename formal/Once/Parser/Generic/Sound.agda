-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Generic.Sound — plan 0.153 D1: soundness of the Acc parser. It
-- recurses on the parser's own `Acc`, step for step (a call on the same input
-- passes the same `Acc`, a call on a shorter one the parser's smaller `Acc`),
-- so the termination checker sees it decrease: no TERMINATING. No `with`, no
-- `rewrite`: a dispatched value is a VARIABLE of a lemma (D0), instantiated
-- with the classifier and `refl`.
------------------------------------------------------------------------

module Once.Parser.Generic.Sound where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (<-trans; n<1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import Once.Spec.Grade using (Many)
open import Once.Parser.Token
open import Once.Parser.Generic.Relation
open import Once.Parser.Generic.Parser hiding (module Make)
import Once.Parser.Generic.Parser
open import Once.Parser.Generic.Complete using (forget-under; forget-after; forget-weaken)

------------------------------------------------------------------------
-- Generic inversions (no recursion), in continuation form.
------------------------------------------------------------------------

map-sound : ∀ {A B n} (g : A → B) (m : Res< A n) {P : B → List Token → Set} {T r}
          → (∀ {a r′} → forget< m ≡ just (a , r′) → P (g a) r′)
          → forget< (mapRes g m) ≡ just (T , r) → P T r
map-sound g (just (a , r′ , q)) k refl = k refl
map-sound g nothing             k ()

under-inv : ∀ {A m n} (p : m < n) (x : Res< A m) {y} → forget< (under p x) ≡ y → forget< x ≡ y
under-inv p x h = trans (sym (forget-under p x)) h

module Make (alg : TyAlg) where
  open TyAlg alg
  open Gen alg
  open Once.Parser.Generic.Parser.Make alg

  parenC-sound : ∀ {A : Set} {P : A → List Token → Set} rest (T : A) r p (v : CloseV r) {T′ r2}
               → P T r → forget< (parenC rest T r p v) ≡ just (T′ , r2) → P T′ (TRParen ∷ r2)
  parenC-sound rest T .(TRParen ∷ r2) p (cR r2)     d refl = d
  parenC-sound rest T r               p (cOther .r) d ()

  parenK-sound : ∀ {A : Set} {P : A → List Token → Set} rest (m : Res< A (length rest)) {T r2}
               → (∀ {T′ r1} → forget< m ≡ just (T′ , r1) → P T′ r1)
               → forget< (parenK rest m) ≡ just (T , r2) → P T (TRParen ∷ r2)
  parenK-sound {P = P} rest (just (T , r , p)) k h = parenC-sound {P = P} rest T r p (closeV r) (k refl) h
  parenK-sound rest nothing k ()

  nuC-sound : ∀ r F r1 p (v : CloseV r1) {T r2} → ParsesFuncSumG r F r1
            → forget< (nuC r F r1 p v) ≡ just (T , r2) → ParsesAtomG (TWord "Nu" ∷ TLParen ∷ TWord "Act" ∷ r) T r2
  nuC-sound r F .(TRParen ∷ r2) p (cR r2)      d refl = pa-nu-act d
  nuC-sound r F r1              p (cOther .r1) d ()

  nuClose-sound : ∀ r m {T r2} → (∀ {F r1} → forget< m ≡ just (F , r1) → ParsesFuncSumG r F r1)
                → forget< (nuClose r m) ≡ just (T , r2) → ParsesAtomG (TWord "Nu" ∷ TLParen ∷ TWord "Act" ∷ r) T r2
  nuClose-sound r (just (F , r1 , p)) k h = nuC-sound r F r1 p (closeV r1) (k refl) h
  nuClose-sound r nothing k ()

  atomX-sound : ∀ toks a m {T rest}
              → (∀ {T′ r′} → forget< (atomKw toks a) ≡ just (T′ , r′) → ParsesAtomG toks T′ r′)
              → forget< (atomX toks a m) ≡ just (T , rest) → ParsesAtomG toks T rest
  atomX-sound toks a (just (x , r , ex)) k refl = pa-extra ex
  atomX-sound toks a nothing             k h    = k h

  arrK-sound : ∀ f toks t d m {P : R → List Token → Set} {T r}
             → (∀ {B r′} → forget< m ≡ just (B , r′) → P (f B) r′)
             → forget≤ (arrK f toks t d m) ≡ just (T , r) → P T r
  arrK-sound f toks t d (just (B , r′ , p)) k refl = k refl
  arrK-sound f toks t d nothing k ()

  BG : ∀ toks → ArrowDir → Set
  BG toks d = ∀ {q} → d ≡ adG q → length (drop2 toks) < length toks

  mutual
    sound-atom : ∀ toks a {T rest} → forget< (atomA toks a) ≡ just (T , rest) → ParsesAtomG toks T rest
    sound-atom toks a h = atomX-sound toks a (extraP toks) (atomH-sound toks (headV toks) a) h

    atomH-sound : ∀ toks v a {T rest} → forget< (atomH toks v a) ≡ just (T , rest) → ParsesAtomG toks T rest
    atomH-sound .(TWord name ∷ rest) (hWord name rest) a h = kwK-sound name rest (kwV name) a h
    atomH-sound .(TLParen ∷ rest) (hParen rest) (acc rec) h =
      pa-paren (parenK-sound {P = ParsesTypeG rest} rest (typeA rest (rec (n<1+n _)))
                             (sound-type rest (rec (n<1+n _))) h) refl
    atomH-sound toks (hOther .toks) a ()

    kwK-sound : ∀ name rest v a {T r} → forget< (kwK name rest v a) ≡ just (T , r) → ParsesAtomG (TWord name ∷ rest) T r
    kwK-sound .("Unit")  rest vUnit  a refl = pa-unit rest
    kwK-sound .("Void")  rest vVoid  a refl = pa-void rest
    kwK-sound .("Int")   rest vInt   a refl = pa-int rest
    kwK-sound .("Float") rest vFloat a refl = pa-float rest
    kwK-sound .("Eff")   rest vEff (acc rec) h =
      twoK-sound aEff "Eff" rest (atomA rest (rec (n<1+n _))) (acc rec) pa-eff (sound-atom rest (rec (n<1+n _))) h
    kwK-sound .("Act")   rest vAct (acc rec) h =
      twoK-sound aAct "Act" rest (atomA rest (rec (n<1+n _))) (acc rec) pa-act (sound-atom rest (rec (n<1+n _))) h
    kwK-sound .("Mu")    rest vMu  (acc rec) h =
      map-sound aMu (fSumA rest (rec (n<1+n _))) {P = ParsesAtomG (TWord "Mu" ∷ rest)}
        (λ e → pa-mu (sound-fSum rest (rec (n<1+n _)) e)) (under-inv _ _ h)
    kwK-sound .("Nu")    rest vNu  (acc rec) h =
      nuTry-sound rest (acc rec) (fSumA rest (rec (n<1+n _))) (sound-fSum rest (rec (n<1+n _))) h
    kwK-sound name rest (vNone .name) a ()

    twoK-sound : ∀ f name rest m a {T r}
               → (∀ {t2 r′ A B} → ParsesAtomG rest A t2 → ParsesAtomG t2 B r′ → ParsesAtomG (TWord name ∷ rest) (f A B) r′)
               → (∀ {A r1} → forget< m ≡ just (A , r1) → ParsesAtomG rest A r1)
               → forget< (twoK f name rest m a) ≡ just (T , r) → ParsesAtomG (TWord name ∷ rest) T r
    twoK-sound f name rest (just (A , r1 , p)) (acc rec) c sA h =
      map-sound (f A) (atomA r1 (rec (<-trans p (n<1+n _)))) {P = ParsesAtomG (TWord name ∷ rest)}
        (λ e → c (sA refl) (sound-atom r1 (rec (<-trans p (n<1+n _))) e)) (under-inv _ _ h)
    twoK-sound f name rest nothing a c sA ()

    nuTry-sound : ∀ rest a m {T r} → (∀ {F r′} → forget< m ≡ just (F , r′) → ParsesFuncSumG rest F r′)
                → forget< (nuTry rest a m) ≡ just (T , r) → ParsesAtomG (TWord "Nu" ∷ rest) T r
    nuTry-sound rest a (just (F , r1 , p)) sF refl = pa-nu (sF refl)
    nuTry-sound rest a nothing             sF h    = nuAct-sound rest a (actHead? rest) h

    nuAct-sound : ∀ rest a m {T r} → forget< (nuAct rest a m) ≡ just (T , r) → ParsesAtomG (TWord "Nu" ∷ rest) T r
    nuAct-sound rest a nothing ()
    nuAct-sound .(TLParen ∷ TWord "Act" ∷ r) (acc rec) (just (r , refl)) h =
      nuClose-sound r (fSumA r (rec (<3 _))) (sound-fSum r (rec (<3 _))) h

    sound-prod : ∀ toks a {T rest} → forget< (prodA toks a) ≡ just (T , rest) → ParsesProdG toks T rest
    sound-prod toks a h = prodK-sound toks (atomA toks a) a (sound-atom toks a) h

    prodK-sound : ∀ toks m a {T rest} → (∀ {A r1} → forget< m ≡ just (A , r1) → ParsesAtomG toks A r1)
                → forget< (prodK toks m a) ≡ just (T , rest) → ParsesProdG toks T rest
    prodK-sound toks (just (A , r1 , p)) (acc rec) sA h =
      pp-mk (sA refl) (sound-prodTail A r1 (rec p) (trans (sym (forget-after p _)) h))
    prodK-sound toks nothing a sA ()

    sound-prodTail : ∀ l toks a {T rest} → forget≤ (prodTailA l toks a) ≡ just (T , rest) → ParsesProdTailG l toks T rest
    sound-prodTail l toks a h = ptGo-sound l toks (isStar toks) (isStar-< toks) a refl h

    ptGo-sound : ∀ l toks b (bnd : b ≡ true → length (drop1 toks) < length toks) a {T rest} → isStar toks ≡ b
               → forget≤ (ptGo l toks b bnd a) ≡ just (T , rest) → ParsesProdTailG l toks T rest
    ptGo-sound l toks false bnd a eq refl = ppt-done eq
    ptGo-sound l toks true bnd (acc rec) eq h =
      ptK-sound l toks (bnd refl) (atomA (drop1 toks) (rec (bnd refl))) (acc rec) eq
                (sound-atom (drop1 toks) (rec (bnd refl))) h

    ptK-sound : ∀ l toks d m a {T rest} → isStar toks ≡ true
              → (∀ {B r2} → forget< m ≡ just (B , r2) → ParsesAtomG (drop1 toks) B r2)
              → forget≤ (ptK l toks d m a) ≡ just (T , rest) → ParsesProdTailG l toks T rest
    ptK-sound l toks d (just (B , r2 , p)) (acc rec) eq sB h =
      ppt-star eq (sB refl) (sound-prodTail (aProd l B) r2 (rec (<-trans p d))
                               (trans (sym (forget-after _ _)) (trans (sym (forget-weaken _)) h)))
    ptK-sound l toks d nothing a eq sB ()

    sound-sum : ∀ toks a {T rest} → forget< (sumA toks a) ≡ just (T , rest) → ParsesSumG toks T rest
    sound-sum toks a h = sumK-sound toks (prodA toks a) a (sound-prod toks a) h

    sumK-sound : ∀ toks m a {T rest} → (∀ {A r1} → forget< m ≡ just (A , r1) → ParsesProdG toks A r1)
               → forget< (sumK toks m a) ≡ just (T , rest) → ParsesSumG toks T rest
    sumK-sound toks (just (A , r1 , p)) (acc rec) sA h =
      ps-mk (sA refl) (sound-sumTail A r1 (rec p) (trans (sym (forget-after p _)) h))
    sumK-sound toks nothing a sA ()

    sound-sumTail : ∀ l toks a {T rest} → forget≤ (sumTailA l toks a) ≡ just (T , rest) → ParsesSumTailG l toks T rest
    sound-sumTail l toks a h = stGo-sound l toks (isPlus toks) (isPlus-< toks) a refl h

    stGo-sound : ∀ l toks b (bnd : b ≡ true → length (drop1 toks) < length toks) a {T rest} → isPlus toks ≡ b
               → forget≤ (stGo l toks b bnd a) ≡ just (T , rest) → ParsesSumTailG l toks T rest
    stGo-sound l toks false bnd a eq refl = pst-done eq
    stGo-sound l toks true bnd (acc rec) eq h =
      stK-sound l toks (bnd refl) (prodA (drop1 toks) (rec (bnd refl))) (acc rec) eq
                (sound-prod (drop1 toks) (rec (bnd refl))) h

    stK-sound : ∀ l toks d m a {T rest} → isPlus toks ≡ true
              → (∀ {B r2} → forget< m ≡ just (B , r2) → ParsesProdG (drop1 toks) B r2)
              → forget≤ (stK l toks d m a) ≡ just (T , rest) → ParsesSumTailG l toks T rest
    stK-sound l toks d (just (B , r2 , p)) (acc rec) eq sB h =
      pst-plus eq (sB refl) (sound-sumTail (aSum l B) r2 (rec (<-trans p d))
                               (trans (sym (forget-after _ _)) (trans (sym (forget-weaken _)) h)))
    stK-sound l toks d nothing a eq sB ()

    sound-type : ∀ toks a {T rest} → forget< (typeA toks a) ≡ just (T , rest) → ParsesTypeG toks T rest
    sound-type toks a h = typeK-sound toks (sumA toks a) a (sound-sum toks a) h

    typeK-sound : ∀ toks m a {T rest} → (∀ {A r1} → forget< m ≡ just (A , r1) → ParsesSumG toks A r1)
                → forget< (typeK toks m a) ≡ just (T , rest) → ParsesTypeG toks T rest
    typeK-sound toks (just (A , r1 , p)) (acc rec) sA h =
      pt-mk (sA refl) (sound-arrowTail A r1 (rec p) (trans (sym (forget-after p _)) h))
    typeK-sound toks nothing a sA ()

    sound-arrowTail : ∀ l toks a {T rest} → forget≤ (arrowTailA l toks a) ≡ just (T , rest) → ParsesArrowTailG l toks T rest
    sound-arrowTail l toks a h = atGo-sound l toks (arrowDir toks) (arrowDir-A-< toks) (arrowDir-G-< toks) a refl h

    atGo-sound : ∀ l toks d (bA : d ≡ adA → length (drop1 toks) < length toks) (bG : BG toks d) a {T rest}
               → arrowDir toks ≡ d → forget≤ (atGo l toks d bA bG a) ≡ just (T , rest) → ParsesArrowTailG l toks T rest
    atGo-sound l toks adD bA bG a eq refl = pat-done eq
    atGo-sound l toks adR bA bG a eq ()
    atGo-sound l toks adA bA bG (acc rec) eq h =
      arrK-sound (aArrow Many l) toks (drop1 toks) (bA refl) (typeA (drop1 toks) (rec (bA refl)))
        {P = ParsesArrowTailG l toks} (λ e → pat-arrow eq (sound-type (drop1 toks) (rec (bA refl)) e)) h
    atGo-sound l toks (adG q) bA bG (acc rec) eq h =
      arrK-sound (aArrow q l) toks (drop2 toks) (bG refl) (typeA (drop2 toks) (rec (bG refl)))
        {P = ParsesArrowTailG l toks} (λ e → pat-arrow-g eq (sound-type (drop2 toks) (rec (bG refl)) e)) h

    sound-fAtom : ∀ toks a {F rest} → forget< (fAtomA toks a) ≡ just (F , rest) → ParsesFuncAtomG toks F rest
    sound-fAtom toks a h = fAtomH-sound toks (headV toks) a h

    fAtomH-sound : ∀ toks v a {F rest} → forget< (fAtomH toks v a) ≡ just (F , rest) → ParsesFuncAtomG toks F rest
    fAtomH-sound .(TWord name ∷ rest) (hWord name rest) a h = fkwK-sound name rest (fkwV name) a h
    fAtomH-sound .(TLParen ∷ rest) (hParen rest) (acc rec) h =
      pfa-paren (parenK-sound {P = ParsesFuncSumG rest} rest (fSumA rest (rec (n<1+n _)))
                              (sound-fSum rest (rec (n<1+n _))) h) refl
    fAtomH-sound toks (hOther .toks) a ()

    fkwK-sound : ∀ name rest v a {F r} → forget< (fkwK name rest v a) ≡ just (F , r) → ParsesFuncAtomG (TWord name ∷ rest) F r
    fkwK-sound .("Id") rest fvId a refl = pfa-id rest
    fkwK-sound .("K")  rest fvK (acc rec) h =
      map-sound fK (atomA rest (rec (n<1+n _))) {P = ParsesFuncAtomG (TWord "K" ∷ rest)}
        (λ e → pfa-k (sound-atom rest (rec (n<1+n _)) e)) (under-inv _ _ h)
    fkwK-sound name rest (fvNone .name) a ()

    sound-fProd : ∀ toks a {F rest} → forget< (fProdA toks a) ≡ just (F , rest) → ParsesFuncProdG toks F rest
    sound-fProd toks a h = fProdK-sound toks (fAtomA toks a) a (sound-fAtom toks a) h

    fProdK-sound : ∀ toks m a {F rest} → (∀ {A r1} → forget< m ≡ just (A , r1) → ParsesFuncAtomG toks A r1)
                 → forget< (fProdK toks m a) ≡ just (F , rest) → ParsesFuncProdG toks F rest
    fProdK-sound toks (just (A , r1 , p)) (acc rec) sA h =
      pfp-mk (sA refl) (sound-fProdTail A r1 (rec p) (trans (sym (forget-after p _)) h))
    fProdK-sound toks nothing a sA ()

    sound-fProdTail : ∀ l toks a {F rest} → forget≤ (fProdTailA l toks a) ≡ just (F , rest) → ParsesFuncProdTailG l toks F rest
    sound-fProdTail l toks a h = fptGo-sound l toks (isStar toks) (isStar-< toks) a refl h

    fptGo-sound : ∀ l toks b (bnd : b ≡ true → length (drop1 toks) < length toks) a {F rest} → isStar toks ≡ b
                → forget≤ (fptGo l toks b bnd a) ≡ just (F , rest) → ParsesFuncProdTailG l toks F rest
    fptGo-sound l toks false bnd a eq refl = pfpt-done eq
    fptGo-sound l toks true bnd (acc rec) eq h =
      fptK-sound l toks (bnd refl) (fAtomA (drop1 toks) (rec (bnd refl))) (acc rec) eq
                 (sound-fAtom (drop1 toks) (rec (bnd refl))) h

    fptK-sound : ∀ l toks d m a {F rest} → isStar toks ≡ true
               → (∀ {B r2} → forget< m ≡ just (B , r2) → ParsesFuncAtomG (drop1 toks) B r2)
               → forget≤ (fptK l toks d m a) ≡ just (F , rest) → ParsesFuncProdTailG l toks F rest
    fptK-sound l toks d (just (B , r2 , p)) (acc rec) eq sB h =
      pfpt-star eq (sB refl) (sound-fProdTail (fProd l B) r2 (rec (<-trans p d))
                                (trans (sym (forget-after _ _)) (trans (sym (forget-weaken _)) h)))
    fptK-sound l toks d nothing a eq sB ()

    sound-fSum : ∀ toks a {F rest} → forget< (fSumA toks a) ≡ just (F , rest) → ParsesFuncSumG toks F rest
    sound-fSum toks a h = fSumK-sound toks (fProdA toks a) a (sound-fProd toks a) h

    fSumK-sound : ∀ toks m a {F rest} → (∀ {A r1} → forget< m ≡ just (A , r1) → ParsesFuncProdG toks A r1)
                → forget< (fSumK toks m a) ≡ just (F , rest) → ParsesFuncSumG toks F rest
    fSumK-sound toks (just (A , r1 , p)) (acc rec) sA h =
      pfs-mk (sA refl) (sound-fSumTail A r1 (rec p) (trans (sym (forget-after p _)) h))
    fSumK-sound toks nothing a sA ()

    sound-fSumTail : ∀ l toks a {F rest} → forget≤ (fSumTailA l toks a) ≡ just (F , rest) → ParsesFuncSumTailG l toks F rest
    sound-fSumTail l toks a h = fstGo-sound l toks (isPlus toks) (isPlus-< toks) a refl h

    fstGo-sound : ∀ l toks b (bnd : b ≡ true → length (drop1 toks) < length toks) a {F rest} → isPlus toks ≡ b
                → forget≤ (fstGo l toks b bnd a) ≡ just (F , rest) → ParsesFuncSumTailG l toks F rest
    fstGo-sound l toks false bnd a eq refl = pfst-done eq
    fstGo-sound l toks true bnd (acc rec) eq h =
      fstK-sound l toks (bnd refl) (fProdA (drop1 toks) (rec (bnd refl))) (acc rec) eq
                 (sound-fProd (drop1 toks) (rec (bnd refl))) h

    fstK-sound : ∀ l toks d m a {F rest} → isPlus toks ≡ true
               → (∀ {B r2} → forget< m ≡ just (B , r2) → ParsesFuncProdG (drop1 toks) B r2)
               → forget≤ (fstK l toks d m a) ≡ just (F , rest) → ParsesFuncSumTailG l toks F rest
    fstK-sound l toks d (just (B , r2 , p)) (acc rec) eq sB h =
      pfst-plus eq (sB refl) (sound-fSumTail (fSum l B) r2 (rec (<-trans p d))
                                (trans (sym (forget-after _ _)) (trans (sym (forget-weaken _)) h)))
    fstK-sound l toks d nothing a eq sB ()

  ----------------------------------------------------------------------
  -- The public statements, over the bound-free parsers.
  ----------------------------------------------------------------------

  sound-atomP : ∀ toks {T rest} → atomP toks ≡ just (T , rest) → ParsesAtomG toks T rest
  sound-atomP toks = sound-atom toks (<-wellFounded _)

  sound-typeP : ∀ toks {T rest} → typeP toks ≡ just (T , rest) → ParsesTypeG toks T rest
  sound-typeP toks = sound-type toks (<-wellFounded _)

  sound-fSumP : ∀ toks {F rest} → fSumP toks ≡ just (F , rest) → ParsesFuncSumG toks F rest
  sound-fSumP toks = sound-fSum toks (<-wellFounded _)
