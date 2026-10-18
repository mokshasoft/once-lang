-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.GenTypes — the compiler's generic type
-- grammar (`Once.Parser.Generic.Relation.Gen`, over a `TyAlg`) against the
-- Spec's (`Once.Spec.Surface.Grammar.Types`, over a `TypeAlg`).
--
-- Given a homomorphism `h` from the compiler's algebra to the Spec's (and
-- what each takes for an extra atom, related both ways), a compiler
-- derivation over `toks` gives a Spec derivation over `map forget toks` of
-- the image, and a Spec derivation over `map forget toks` comes from a
-- compiler derivation over `toks`.
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.GenTypes where

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

import Once.Lang.Type.Grade as LG
import Once.Spec.Grade as SG
open import Once.Spec.Surface.Lexing using (Token; TWord; TLParen; TRParen; TArrow; TCaret0; TCaret1; TCaretW; TStar; TPlus)
open import Once.Spec.Surface.Grammar using (TypeAlg; module Types; Starts; starts; GradeToken; g0; g1; gw)
import Once.Parser.Token as P
open import Once.Parser.Generic.Relation using (TyAlg; module Gen; adG; adA; adD; ArrowDir; arrowDir; drop1; drop2)
open import Once.Adequacy.SpecGrammar.Tokens using (forget; step; peel)
open import Once.Adequacy.SpecGrammar.TypeHeads
  using (star-false→; star-false←; star-true; plus-false→; plus-false←; plus-true; ArrowView; arrow-view;
         av-g1; av-g0; av-gw; av-a; av-r; av-d; ic0; ic1; icw)
open import Once.Adequacy.SpecGrammar.Conv using (qS)

private
  F : List P.Token → List Token
  F = map forget

-- What a homomorphism owes.
module _ (alg : TyAlg) {R′ RF′ : Set} (salg : TypeAlg R′ RF′) where
  private
    module O = TyAlg alg
    module S = TypeAlg salg

  record Hom (h : O.R → R′) (hF : O.RF → RF′) : Set₁ where
    field
      h-unit  : h O.aUnit ≡ S.aUnit
      h-void  : h O.aVoid ≡ S.aVoid
      h-int   : h O.aInt ≡ S.aInt
      h-float : h O.aFloat ≡ S.aFloat
      h-prod  : ∀ a b → h (O.aProd a b) ≡ S.aProd (h a) (h b)
      h-sum   : ∀ a b → h (O.aSum a b) ≡ S.aSum (h a) (h b)
      h-eff   : ∀ a b → h (O.aEff a b) ≡ S.aEff (h a) (h b)
      h-act   : ∀ a b → h (O.aAct a b) ≡ S.aAct (h a) (h b)
      h-arrow : ∀ q a b → h (O.aArrow q a b) ≡ S.aArrow (qS q) (h a) (h b)
      h-mu    : ∀ f → h (O.aMu f) ≡ S.aMu (hF f)
      h-nu    : ∀ f → h (O.aNu f) ≡ S.aNu SG.pure (hF f)
      h-nueff : ∀ f → h (O.aNuEff f) ≡ S.aNu SG.eff (hF f)
      h-nuact : ∀ f → h (O.aNuAct f) ≡ S.aNu SG.act (hF f)
      hF-k    : ∀ a → hF (O.fK a) ≡ S.fK (h a)
      hF-id   : hF O.fId ≡ S.fId
      hF-sum  : ∀ f g → hF (O.fSum f g) ≡ S.fSum (hF f) (hF g)
      hF-prod : ∀ f g → hF (O.fProd f g) ≡ S.fProd (hF f) (hF g)
      extra→  : ∀ {toks a rest} → O.Extra toks a rest → S.Extra (F toks) (h a) (F rest)
      extra←  : ∀ {ts a′ r′} → S.Extra ts a′ r′ → ∀ toks → F toks ≡ ts
              → Σ[ a ∈ O.R ] Σ[ rest ∈ List P.Token ] (O.Extra toks a rest × h a ≡ a′ × F rest ≡ r′)

module Bridge (alg : TyAlg) {R′ RF′ : Set} (salg : TypeAlg R′ RF′)
              (h : TyAlg.R alg → R′) (hF : TyAlg.RF alg → RF′) (hom : Hom alg salg h hF) where
  open TyAlg alg
  open Gen alg
  private module S = TypeAlg salg
  open Types salg
  open Hom hom

  ----------------------------------------------------------------------
  -- The compiler's derivation gives the Spec's
  ----------------------------------------------------------------------

  atom→      : ∀ {toks a rest} → ParsesAtomG toks a rest → ParsesAtom (F toks) (h a) (F rest)
  prod→      : ∀ {toks a rest} → ParsesProdG toks a rest → ParsesProd (F toks) (h a) (F rest)
  ptail→     : ∀ {l toks a rest} → ParsesProdTailG l toks a rest → ParsesProdTail (h l) (F toks) (h a) (F rest)
  sum→       : ∀ {toks a rest} → ParsesSumG toks a rest → ParsesSum (F toks) (h a) (F rest)
  stail→     : ∀ {l toks a rest} → ParsesSumTailG l toks a rest → ParsesSumTail (h l) (F toks) (h a) (F rest)
  type→      : ∀ {toks a rest} → ParsesTypeG toks a rest → ParsesType (F toks) (h a) (F rest)
  atail→     : ∀ {l toks a rest} → ParsesArrowTailG l toks a rest → ParsesArrowTail (h l) (F toks) (h a) (F rest)
  fatom→     : ∀ {toks f rest} → ParsesFuncAtomG toks f rest → ParsesFunAtom (F toks) (hF f) (F rest)
  fprod→     : ∀ {toks f rest} → ParsesFuncProdG toks f rest → ParsesFunProd (F toks) (hF f) (F rest)
  fptail→    : ∀ {l toks f rest} → ParsesFuncProdTailG l toks f rest → ParsesFunProdTail (hF l) (F toks) (hF f) (F rest)
  fsum→      : ∀ {toks f rest} → ParsesFuncSumG toks f rest → ParsesFunSum (F toks) (hF f) (F rest)
  fstail→    : ∀ {l toks f rest} → ParsesFuncSumTailG l toks f rest → ParsesFunSumTail (hF l) (F toks) (hF f) (F rest)

  private
    atomAt : ∀ {ts r x y} → x ≡ y → ParsesAtom ts x r → ParsesAtom ts y r
    atomAt e d = subst (λ z → ParsesAtom _ z _) e d

    fatomAt : ∀ {ts r x y} → x ≡ y → ParsesFunAtom ts x r → ParsesFunAtom ts y r
    fatomAt e d = subst (λ z → ParsesFunAtom _ z _) e d

    pstar : ∀ {l toks B toks₂ a rest} → Σ[ t ∈ List P.Token ] toks ≡ P.TStar ∷ t
          → ParsesAtomG (drop1 toks) B toks₂ → ParsesProdTailG (aProd l B) toks₂ a rest
          → ParsesProdTail (h l) (F toks) (h a) (F rest)

    splus : ∀ {l toks B toks₂ a rest} → Σ[ t ∈ List P.Token ] toks ≡ P.TPlus ∷ t
          → ParsesProdG (drop1 toks) B toks₂ → ParsesSumTailG (aSum l B) toks₂ a rest
          → ParsesSumTail (h l) (F toks) (h a) (F rest)

  atom→ (pa-unit _)  = atomAt (sym h-unit) a-unit
  atom→ (pa-void _)  = atomAt (sym h-void) a-void
  atom→ (pa-int _)   = atomAt (sym h-int) a-int
  atom→ (pa-float _) = atomAt (sym h-float) a-float
  atom→ (pa-eff dA dB) = atomAt (sym (h-eff _ _)) (a-eff (atom→ dA) (atom→ dB))
  atom→ (pa-act dA dB) = atomAt (sym (h-act _ _)) (a-act (atom→ dA) (atom→ dB))
  atom→ (pa-mu dF) = atomAt (sym (h-mu _)) (a-mu (fsum→ dF))
  atom→ (pa-nu dF) = atomAt (sym (h-nu _)) (a-nu (fsum→ dF))
  atom→ (pa-nu-eff dF) = atomAt (sym (h-nueff _)) (a-nu-eff (fsum→ dF))
  atom→ (pa-nu-act dF) = atomAt (sym (h-nuact _)) (a-nu-act (fsum→ dF))
  atom→ (pa-extra ex) = a-extra (extra→ ex)
  atom→ (pa-paren dT refl) = a-paren (type→ dT)

  prod→ (pp-mk dA dT) = prod (atom→ dA) (ptail→ dT)

  ptail→ {toks = toks} (ppt-done e) = prod-done (star-false→ toks e)
  ptail→ {toks = toks} (ppt-star e dB dT) = pstar (star-true toks e) dB dT

  pstar (t , refl) dB dT = prod-star (atom→ dB) (subst (λ z → ParsesProdTail z _ _ _) (h-prod _ _) (ptail→ dT))

  sum→ (ps-mk dA dT) = sum (prod→ dA) (stail→ dT)

  stail→ {toks = toks} (pst-done e) = sum-done (plus-false→ toks e)
  stail→ {toks = toks} (pst-plus e dB dT) = splus (plus-true toks e) dB dT

  splus (t , refl) dB dT = sum-plus (prod→ dB) (subst (λ z → ParsesSumTail z _ _ _) (h-sum _ _) (stail→ dT))

  type→ (pt-mk dS dA) = type (sum→ dS) (atail→ dA)

  private
    adone : ∀ {l toks} → ArrowView toks adD → ParsesArrowTail (h l) (F toks) (h l) (F toks)
    adone (av-d a b c d) = arrow-done a b c d

    agrade : ∀ {l toks q B rest} → ArrowView toks (adG q) → ParsesTypeG (drop2 toks) B rest
           → ParsesArrowTail (h l) (F toks) (h (aArrow q l B)) (F rest)
    agrade av-g1 dT = subst (λ z → ParsesArrowTail _ _ z _) (sym (h-arrow _ _ _)) (arrow-grade g1 (type→ dT))
    agrade av-g0 dT = subst (λ z → ParsesArrowTail _ _ z _) (sym (h-arrow _ _ _)) (arrow-grade g0 (type→ dT))
    agrade av-gw dT = subst (λ z → ParsesArrowTail _ _ z _) (sym (h-arrow _ _ _)) (arrow-grade gw (type→ dT))

    aplain : ∀ {l toks B rest} → ArrowView toks adA → ParsesTypeG (drop1 toks) B rest
           → ParsesArrowTail (h l) (F toks) (h (aArrow LG.Many l B)) (F rest)
    aplain av-a dT = subst (λ z → ParsesArrowTail _ _ z _) (sym (h-arrow _ _ _)) (arrow (type→ dT))

  atail→ {toks = toks} (pat-done e) = adone (subst (ArrowView toks) e (arrow-view toks))
  atail→ {toks = toks} (pat-arrow-g e dT) = agrade (subst (ArrowView toks) e (arrow-view toks)) dT
  atail→ {toks = toks} (pat-arrow e dT) = aplain (subst (ArrowView toks) e (arrow-view toks)) dT

  private
    fpstar : ∀ {l toks B toks₂ f rest} → Σ[ t ∈ List P.Token ] toks ≡ P.TStar ∷ t
           → ParsesFuncAtomG (drop1 toks) B toks₂ → ParsesFuncProdTailG (fProd l B) toks₂ f rest
           → ParsesFunProdTail (hF l) (F toks) (hF f) (F rest)
    fsplus : ∀ {l toks B toks₂ f rest} → Σ[ t ∈ List P.Token ] toks ≡ P.TPlus ∷ t
           → ParsesFuncProdG (drop1 toks) B toks₂ → ParsesFuncSumTailG (fSum l B) toks₂ f rest
           → ParsesFunSumTail (hF l) (F toks) (hF f) (F rest)

  fatom→ (pfa-id _) = fatomAt (sym hF-id) f-id
  fatom→ (pfa-k dA) = fatomAt (sym (hF-k _)) (f-k (atom→ dA))
  fatom→ (pfa-paren dF refl) = f-paren (fsum→ dF)

  fprod→ (pfp-mk dA dT) = fprod (fatom→ dA) (fptail→ dT)

  fptail→ {toks = toks} (pfpt-done e) = fprod-done (star-false→ toks e)
  fptail→ {toks = toks} (pfpt-star e dB dT) = fpstar (star-true toks e) dB dT

  fpstar (t , refl) dB dT = fprod-star (fatom→ dB) (subst (λ z → ParsesFunProdTail z _ _ _) (hF-prod _ _) (fptail→ dT))

  fsum→ (pfs-mk dA dT) = fsum (fprod→ dA) (fstail→ dT)

  fstail→ {toks = toks} (pfst-done e) = fsum-done (plus-false→ toks e)
  fstail→ {toks = toks} (pfst-plus e dB dT) = fsplus (plus-true toks e) dB dT

  fsplus (t , refl) dB dT = fsum-plus (fprod→ dB) (subst (λ z → ParsesFunSumTail z _ _ _) (hF-sum _ _) (fstail→ dT))

  ----------------------------------------------------------------------
  -- The Spec's derivation comes from the compiler's
  ----------------------------------------------------------------------

  -- A compiler derivation over `toks` whose image is `a′`, ending where `r′` begins.
  Back : (List P.Token → R → List P.Token → Set) → List P.Token → R′ → List Token → Set
  Back Rel toks a′ r′ = Σ[ a ∈ R ] Σ[ rest ∈ List P.Token ] (Rel toks a rest × h a ≡ a′ × F rest ≡ r′)

  BackF : (List P.Token → RF → List P.Token → Set) → List P.Token → RF′ → List Token → Set
  BackF Rel toks f′ r′ = Σ[ f ∈ RF ] Σ[ rest ∈ List P.Token ] (Rel toks f rest × hF f ≡ f′ × F rest ≡ r′)

  BackT : (R → List P.Token → R → List P.Token → Set) → R → List P.Token → R′ → List Token → Set
  BackT Rel l toks a′ r′ = Σ[ a ∈ R ] Σ[ rest ∈ List P.Token ] (Rel l toks a rest × h a ≡ a′ × F rest ≡ r′)

  BackTF : (RF → List P.Token → RF → List P.Token → Set) → RF → List P.Token → RF′ → List Token → Set
  BackTF Rel l toks f′ r′ = Σ[ f ∈ RF ] Σ[ rest ∈ List P.Token ] (Rel l toks f rest × hF f ≡ f′ × F rest ≡ r′)

  atom←   : ∀ {ts a′ r′} → ParsesAtom ts a′ r′ → ∀ toks → F toks ≡ ts → Back ParsesAtomG toks a′ r′
  prod←   : ∀ {ts a′ r′} → ParsesProd ts a′ r′ → ∀ toks → F toks ≡ ts → Back ParsesProdG toks a′ r′
  ptail←  : ∀ {l′ ts a′ r′} → ParsesProdTail l′ ts a′ r′ → ∀ l toks → h l ≡ l′ → F toks ≡ ts → BackT ParsesProdTailG l toks a′ r′
  sum←    : ∀ {ts a′ r′} → ParsesSum ts a′ r′ → ∀ toks → F toks ≡ ts → Back ParsesSumG toks a′ r′
  stail←  : ∀ {l′ ts a′ r′} → ParsesSumTail l′ ts a′ r′ → ∀ l toks → h l ≡ l′ → F toks ≡ ts → BackT ParsesSumTailG l toks a′ r′
  type←   : ∀ {ts a′ r′} → ParsesType ts a′ r′ → ∀ toks → F toks ≡ ts → Back ParsesTypeG toks a′ r′
  atail←  : ∀ {l′ ts a′ r′} → ParsesArrowTail l′ ts a′ r′ → ∀ l toks → h l ≡ l′ → F toks ≡ ts → BackT ParsesArrowTailG l toks a′ r′
  fatom←  : ∀ {ts f′ r′} → ParsesFunAtom ts f′ r′ → ∀ toks → F toks ≡ ts → BackF ParsesFuncAtomG toks f′ r′
  fprod←  : ∀ {ts f′ r′} → ParsesFunProd ts f′ r′ → ∀ toks → F toks ≡ ts → BackF ParsesFuncProdG toks f′ r′
  fptail← : ∀ {l′ ts f′ r′} → ParsesFunProdTail l′ ts f′ r′ → ∀ l toks → hF l ≡ l′ → F toks ≡ ts → BackTF ParsesFuncProdTailG l toks f′ r′
  fsum←   : ∀ {ts f′ r′} → ParsesFunSum ts f′ r′ → ∀ toks → F toks ≡ ts → BackF ParsesFuncSumG toks f′ r′
  fstail← : ∀ {l′ ts f′ r′} → ParsesFunSumTail l′ ts f′ r′ → ∀ l toks → hF l ≡ l′ → F toks ≡ ts → BackTF ParsesFuncSumTailG l toks f′ r′

  private
    -- the continuations, one per rule with a premise
    eff₁ : ∀ {toks₁ A′ ts₂ B′ r′} → Back ParsesAtomG toks₁ A′ ts₂ → ParsesAtom ts₂ B′ r′
         → Back ParsesAtomG (P.TWord "Eff" ∷ toks₁) (S.aEff A′ B′) r′
    eff₂ : ∀ {toks₁ A toks₂ A′ B′ r′} → ParsesAtomG toks₁ A toks₂ → h A ≡ A′ → Back ParsesAtomG toks₂ B′ r′
         → Back ParsesAtomG (P.TWord "Eff" ∷ toks₁) (S.aEff A′ B′) r′
    act₁ : ∀ {toks₁ A′ ts₂ B′ r′} → Back ParsesAtomG toks₁ A′ ts₂ → ParsesAtom ts₂ B′ r′
         → Back ParsesAtomG (P.TWord "Act" ∷ toks₁) (S.aAct A′ B′) r′
    act₂ : ∀ {toks₁ A toks₂ A′ B′ r′} → ParsesAtomG toks₁ A toks₂ → h A ≡ A′ → Back ParsesAtomG toks₂ B′ r′
         → Back ParsesAtomG (P.TWord "Act" ∷ toks₁) (S.aAct A′ B′) r′
    mu₁  : ∀ {toks₁ F′ r′} → BackF ParsesFuncSumG toks₁ F′ r′ → Back ParsesAtomG (P.TWord "Mu" ∷ toks₁) (S.aMu F′) r′
    nu₁  : ∀ {toks₁ F′ r′} → BackF ParsesFuncSumG toks₁ F′ r′ → Back ParsesAtomG (P.TWord "Nu" ∷ toks₁) (S.aNu SG.pure F′) r′
    nueff₁ : ∀ {toks₁ F′ r′} → BackF ParsesFuncSumG toks₁ F′ (TRParen ∷ r′)
           → Back ParsesAtomG (P.TWord "Nu" ∷ P.TLParen ∷ P.TWord "Eff" ∷ toks₁) (S.aNu SG.eff F′) r′
    nueff₂ : ∀ {toks₁ f rest F′ r′} → ParsesFuncSumG toks₁ f rest → hF f ≡ F′
           → Σ[ rest′ ∈ List P.Token ] (rest ≡ P.TRParen ∷ rest′ × F rest′ ≡ r′)
           → Back ParsesAtomG (P.TWord "Nu" ∷ P.TLParen ∷ P.TWord "Eff" ∷ toks₁) (S.aNu SG.eff F′) r′
    nuact₁ : ∀ {toks₁ F′ r′} → BackF ParsesFuncSumG toks₁ F′ (TRParen ∷ r′)
           → Back ParsesAtomG (P.TWord "Nu" ∷ P.TLParen ∷ P.TWord "Act" ∷ toks₁) (S.aNu SG.act F′) r′
    nuact₂ : ∀ {toks₁ f rest F′ r′} → ParsesFuncSumG toks₁ f rest → hF f ≡ F′
           → Σ[ rest′ ∈ List P.Token ] (rest ≡ P.TRParen ∷ rest′ × F rest′ ≡ r′)
           → Back ParsesAtomG (P.TWord "Nu" ∷ P.TLParen ∷ P.TWord "Act" ∷ toks₁) (S.aNu SG.act F′) r′
    paren₁ : ∀ {toks₁ A′ r′} → Back ParsesTypeG toks₁ A′ (TRParen ∷ r′) → Back ParsesAtomG (P.TLParen ∷ toks₁) A′ r′
    paren₂ : ∀ {toks₁ a rest A′ r′} → ParsesTypeG toks₁ a rest → h a ≡ A′
           → Σ[ rest′ ∈ List P.Token ] (rest ≡ P.TRParen ∷ rest′ × F rest′ ≡ r′)
           → Back ParsesAtomG (P.TLParen ∷ toks₁) A′ r′
    extra₁ : ∀ {toks a′ r′} → Σ[ a ∈ R ] Σ[ rest ∈ List P.Token ] (Extra toks a rest × h a ≡ a′ × F rest ≡ r′)
           → Back ParsesAtomG toks a′ r′

  eff₁ (A , toks₂ , dA , hA , e₂) dB = eff₂ dA hA (atom← dB toks₂ e₂)
  eff₂ {A = A} dA hA (B , rest , dB , hB , er) = aEff A B , rest , pa-eff dA dB , trans (h-eff A B) (cong₂ S.aEff hA hB) , er
  act₁ (A , toks₂ , dA , hA , e₂) dB = act₂ dA hA (atom← dB toks₂ e₂)
  act₂ {A = A} dA hA (B , rest , dB , hB , er) = aAct A B , rest , pa-act dA dB , trans (h-act A B) (cong₂ S.aAct hA hB) , er
  mu₁ (f , rest , dF , hf , er) = aMu f , rest , pa-mu dF , trans (h-mu f) (cong S.aMu hf) , er
  nu₁ (f , rest , dF , hf , er) = aNu f , rest , pa-nu dF , trans (h-nu f) (cong (S.aNu SG.pure) hf) , er
  nueff₁ (f , rest , dF , hf , er) = nueff₂ dF hf (peel refl er)
  nueff₂ {f = f} dF hf (rest′ , refl , er) = aNuEff f , rest′ , pa-nu-eff dF , trans (h-nueff f) (cong (S.aNu SG.eff) hf) , er
  nuact₁ (f , rest , dF , hf , er) = nuact₂ dF hf (peel refl er)
  nuact₂ {f = f} dF hf (rest′ , refl , er) = aNuAct f , rest′ , pa-nu-act dF , trans (h-nuact f) (cong (S.aNu SG.act) hf) , er
  paren₁ (a , rest , dT , ha , er) = paren₂ dT ha (peel refl er)
  paren₂ {a = a} dT ha (rest′ , refl , er) = a , rest′ , pa-paren dT refl , ha , er
  extra₁ (a , rest , ex , ha , er) = a , rest , pa-extra ex , ha , er

  atom← a-unit toks e = step (λ x → Back ParsesAtomG x S.aUnit _) refl e (λ {toks′} e′ → aUnit , toks′ , pa-unit toks′ , h-unit , e′)
  atom← a-void toks e = step (λ x → Back ParsesAtomG x S.aVoid _) refl e (λ {toks′} e′ → aVoid , toks′ , pa-void toks′ , h-void , e′)
  atom← a-int toks e = step (λ x → Back ParsesAtomG x S.aInt _) refl e (λ {toks′} e′ → aInt , toks′ , pa-int toks′ , h-int , e′)
  atom← a-float toks e = step (λ x → Back ParsesAtomG x S.aFloat _) refl e (λ {toks′} e′ → aFloat , toks′ , pa-float toks′ , h-float , e′)
  atom← (a-eff dA dB) toks e = step (λ x → Back ParsesAtomG x _ _) refl e (λ {toks′} e′ → eff₁ (atom← dA toks′ e′) dB)
  atom← (a-act dA dB) toks e = step (λ x → Back ParsesAtomG x _ _) refl e (λ {toks′} e′ → act₁ (atom← dA toks′ e′) dB)
  atom← (a-mu dF) toks e = step (λ x → Back ParsesAtomG x _ _) refl e (λ {toks′} e′ → mu₁ (fsum← dF toks′ e′))
  atom← (a-nu dF) toks e = step (λ x → Back ParsesAtomG x _ _) refl e (λ {toks′} e′ → nu₁ (fsum← dF toks′ e′))
  atom← (a-nu-eff dF) toks e =
    step (λ x → Back ParsesAtomG x _ _) refl e (λ e₁ →
    step (λ x → Back ParsesAtomG (P.TWord "Nu" ∷ x) _ _) refl e₁ (λ e₂ →
    step (λ x → Back ParsesAtomG (P.TWord "Nu" ∷ P.TLParen ∷ x) _ _) refl e₂ (λ {toks′} e₃ →
    nueff₁ (fsum← dF toks′ e₃))))
  atom← (a-nu-act dF) toks e =
    step (λ x → Back ParsesAtomG x _ _) refl e (λ e₁ →
    step (λ x → Back ParsesAtomG (P.TWord "Nu" ∷ x) _ _) refl e₁ (λ e₂ →
    step (λ x → Back ParsesAtomG (P.TWord "Nu" ∷ P.TLParen ∷ x) _ _) refl e₂ (λ {toks′} e₃ →
    nuact₁ (fsum← dF toks′ e₃))))
  atom← (a-extra ex) toks e = extra₁ (extra← ex toks e)
  atom← (a-paren dT) toks e = step (λ x → Back ParsesAtomG x _ _) refl e (λ {toks′} e′ → paren₁ (type← dT toks′ e′))

  private
    prod₁ : ∀ {toks a′ ts₁ T′ r′} → Back ParsesAtomG toks a′ ts₁ → ParsesProdTail a′ ts₁ T′ r′ → Back ParsesProdG toks T′ r′
    prod₂ : ∀ {toks a toks₁ T′ r′} → ParsesAtomG toks a toks₁ → BackT ParsesProdTailG a toks₁ T′ r′ → Back ParsesProdG toks T′ r′
    pstar₁ : ∀ {l toks₁ B′ ts₂ l′ T′ r′} → h l ≡ l′ → Back ParsesAtomG toks₁ B′ ts₂ → ParsesProdTail (S.aProd l′ B′) ts₂ T′ r′
           → BackT ParsesProdTailG l (P.TStar ∷ toks₁) T′ r′
    pstar₂ : ∀ {l toks₁ B toks₂ T′ r′} → ParsesAtomG toks₁ B toks₂ → BackT ParsesProdTailG (aProd l B) toks₂ T′ r′
           → BackT ParsesProdTailG l (P.TStar ∷ toks₁) T′ r′

  prod₁ (a , toks₁ , dA , ha , e₁) dT = prod₂ dA (ptail← dT a toks₁ ha e₁)
  prod₂ dA (T , rest , dT , hT , er) = T , rest , pp-mk dA dT , hT , er
  pstar₁ {l = l} hl (B , toks₂ , dB , hB , e₂) dT = pstar₂ dB (ptail← dT (aProd l B) toks₂ (trans (h-prod l B) (cong₂ S.aProd hl hB)) e₂)
  pstar₂ dB (T , rest , dT , hT , er) = T , rest , ppt-star refl dB dT , hT , er

  prod← (prod dA dT) toks e = prod₁ (atom← dA toks e) dT

  ptail← (prod-done n) l toks refl refl = l , toks , ppt-done (star-false← toks n) , refl , refl
  ptail← (prod-star dB dT) l toks hl e =
    step (λ x → BackT ParsesProdTailG l x _ _) refl e (λ {toks′} e′ → pstar₁ hl (atom← dB toks′ e′) dT)

  private
    sum₁ : ∀ {toks a′ ts₁ T′ r′} → Back ParsesProdG toks a′ ts₁ → ParsesSumTail a′ ts₁ T′ r′ → Back ParsesSumG toks T′ r′
    sum₂ : ∀ {toks a toks₁ T′ r′} → ParsesProdG toks a toks₁ → BackT ParsesSumTailG a toks₁ T′ r′ → Back ParsesSumG toks T′ r′
    splus₁ : ∀ {l toks₁ B′ ts₂ l′ T′ r′} → h l ≡ l′ → Back ParsesProdG toks₁ B′ ts₂ → ParsesSumTail (S.aSum l′ B′) ts₂ T′ r′
           → BackT ParsesSumTailG l (P.TPlus ∷ toks₁) T′ r′
    splus₂ : ∀ {l toks₁ B toks₂ T′ r′} → ParsesProdG toks₁ B toks₂ → BackT ParsesSumTailG (aSum l B) toks₂ T′ r′
           → BackT ParsesSumTailG l (P.TPlus ∷ toks₁) T′ r′

  sum₁ (a , toks₁ , dA , ha , e₁) dT = sum₂ dA (stail← dT a toks₁ ha e₁)
  sum₂ dA (T , rest , dT , hT , er) = T , rest , ps-mk dA dT , hT , er
  splus₁ {l = l} hl (B , toks₂ , dB , hB , e₂) dT = splus₂ dB (stail← dT (aSum l B) toks₂ (trans (h-sum l B) (cong₂ S.aSum hl hB)) e₂)
  splus₂ dB (T , rest , dT , hT , er) = T , rest , pst-plus refl dB dT , hT , er

  sum← (sum dA dT) toks e = sum₁ (prod← dA toks e) dT

  stail← (sum-done n) l toks refl refl = l , toks , pst-done (plus-false← toks n) , refl , refl
  stail← (sum-plus dB dT) l toks hl e =
    step (λ x → BackT ParsesSumTailG l x _ _) refl e (λ {toks′} e′ → splus₁ hl (prod← dB toks′ e′) dT)

  private
    type₁ : ∀ {toks a′ ts₁ T′ r′} → Back ParsesSumG toks a′ ts₁ → ParsesArrowTail a′ ts₁ T′ r′ → Back ParsesTypeG toks T′ r′
    type₂ : ∀ {toks a toks₁ T′ r′} → ParsesSumG toks a toks₁ → BackT ParsesArrowTailG a toks₁ T′ r′ → Back ParsesTypeG toks T′ r′
    done-dir : ∀ toks {k} → ¬ (Starts (F toks) TArrow) → ¬ (Starts (F toks) TCaret0) → ¬ (Starts (F toks) TCaret1)
             → ¬ (Starts (F toks) TCaretW) → ArrowView toks k → k ≡ adD
    graded : ∀ {l q′ toks₁ B′ l′ r′} (g : P.Token) (q : LG.Quantity) → (∀ t → arrowDir (g ∷ P.TArrow ∷ t) ≡ adG q)
           → qS q ≡ q′ → h l ≡ l′ → Back ParsesTypeG toks₁ B′ r′
           → BackT ParsesArrowTailG l (g ∷ P.TArrow ∷ toks₁) (S.aArrow q′ l′ B′) r′
    plain : ∀ {l toks₁ B′ l′ r′} → h l ≡ l′ → Back ParsesTypeG toks₁ B′ r′
          → BackT ParsesArrowTailG l (P.TArrow ∷ toks₁) (S.aArrow SG.Many l′ B′) r′

  type₁ (a , toks₁ , dS , ha , e₁) dA = type₂ dS (atail← dA a toks₁ ha e₁)
  type₂ dS (T , rest , dA , hT , er) = T , rest , pt-mk dS dA , hT , er

  type← (type dS dA) toks e = type₁ (sum← dS toks e) dA

  done-dir _ a b c d av-g1 = ⊥-elim (c starts)
  done-dir _ a b c d av-g0 = ⊥-elim (b starts)
  done-dir _ a b c d av-gw = ⊥-elim (d starts)
  done-dir _ a b c d av-a = ⊥-elim (a starts)
  done-dir _ a b c d (av-r ic0) = ⊥-elim (b starts)
  done-dir _ a b c d (av-r ic1) = ⊥-elim (c starts)
  done-dir _ a b c d (av-r icw) = ⊥-elim (d starts)
  done-dir toks a b c d (av-d _ _ _ _) = refl

  graded {l = l} g q dir refl hl (B , rest , dB , hB , er) =
    aArrow q l B , rest , pat-arrow-g (dir _) dB , trans (h-arrow q l B) (cong₂ (S.aArrow (qS q)) hl hB) , er
  plain {l = l} hl (B , rest , dB , hB , er) =
    aArrow LG.Many l B , rest , pat-arrow refl dB , trans (h-arrow LG.Many l B) (cong₂ (S.aArrow SG.Many) hl hB) , er

  atail← (arrow-done a b c d) l toks refl refl =
    l , toks , pat-done (done-dir toks a b c d (arrow-view toks)) , refl , refl
  atail← (arrow-grade g0 dT) l toks hl e =
    step (λ x → BackT ParsesArrowTailG l x _ _) refl e (λ e₁ →
    step (λ x → BackT ParsesArrowTailG l (P.TCaret0 ∷ x) _ _) refl e₁ (λ {toks′} e₂ →
    graded P.TCaret0 LG.Zero (λ _ → refl) refl hl (type← dT toks′ e₂)))
  atail← (arrow-grade g1 dT) l toks hl e =
    step (λ x → BackT ParsesArrowTailG l x _ _) refl e (λ e₁ →
    step (λ x → BackT ParsesArrowTailG l (P.TCaret1 ∷ x) _ _) refl e₁ (λ {toks′} e₂ →
    graded P.TCaret1 LG.One (λ _ → refl) refl hl (type← dT toks′ e₂)))
  atail← (arrow-grade gw dT) l toks hl e =
    step (λ x → BackT ParsesArrowTailG l x _ _) refl e (λ e₁ →
    step (λ x → BackT ParsesArrowTailG l (P.TCaretW ∷ x) _ _) refl e₁ (λ {toks′} e₂ →
    graded P.TCaretW LG.Many (λ _ → refl) refl hl (type← dT toks′ e₂)))
  atail← (arrow dT) l toks hl e =
    step (λ x → BackT ParsesArrowTailG l x _ _) refl e (λ {toks′} e′ → plain hl (type← dT toks′ e′))

  private
    fk₁ : ∀ {toks₁ A′ r′} → Back ParsesAtomG toks₁ A′ r′ → BackF ParsesFuncAtomG (P.TWord "K" ∷ toks₁) (S.fK A′) r′
    fparen₁ : ∀ {toks₁ F′ r′} → BackF ParsesFuncSumG toks₁ F′ (TRParen ∷ r′) → BackF ParsesFuncAtomG (P.TLParen ∷ toks₁) F′ r′
    fparen₂ : ∀ {toks₁ f rest F′ r′} → ParsesFuncSumG toks₁ f rest → hF f ≡ F′
            → Σ[ rest′ ∈ List P.Token ] (rest ≡ P.TRParen ∷ rest′ × F rest′ ≡ r′)
            → BackF ParsesFuncAtomG (P.TLParen ∷ toks₁) F′ r′
    fprod₁ : ∀ {toks a′ ts₁ T′ r′} → BackF ParsesFuncAtomG toks a′ ts₁ → ParsesFunProdTail a′ ts₁ T′ r′ → BackF ParsesFuncProdG toks T′ r′
    fprod₂ : ∀ {toks a toks₁ T′ r′} → ParsesFuncAtomG toks a toks₁ → BackTF ParsesFuncProdTailG a toks₁ T′ r′ → BackF ParsesFuncProdG toks T′ r′
    fpstar₁ : ∀ {l toks₁ B′ ts₂ l′ T′ r′} → hF l ≡ l′ → BackF ParsesFuncAtomG toks₁ B′ ts₂ → ParsesFunProdTail (S.fProd l′ B′) ts₂ T′ r′
            → BackTF ParsesFuncProdTailG l (P.TStar ∷ toks₁) T′ r′
    fpstar₂ : ∀ {l toks₁ B toks₂ T′ r′} → ParsesFuncAtomG toks₁ B toks₂ → BackTF ParsesFuncProdTailG (fProd l B) toks₂ T′ r′
            → BackTF ParsesFuncProdTailG l (P.TStar ∷ toks₁) T′ r′
    fsum₁ : ∀ {toks a′ ts₁ T′ r′} → BackF ParsesFuncProdG toks a′ ts₁ → ParsesFunSumTail a′ ts₁ T′ r′ → BackF ParsesFuncSumG toks T′ r′
    fsum₂ : ∀ {toks a toks₁ T′ r′} → ParsesFuncProdG toks a toks₁ → BackTF ParsesFuncSumTailG a toks₁ T′ r′ → BackF ParsesFuncSumG toks T′ r′
    fsplus₁ : ∀ {l toks₁ B′ ts₂ l′ T′ r′} → hF l ≡ l′ → BackF ParsesFuncProdG toks₁ B′ ts₂ → ParsesFunSumTail (S.fSum l′ B′) ts₂ T′ r′
            → BackTF ParsesFuncSumTailG l (P.TPlus ∷ toks₁) T′ r′
    fsplus₂ : ∀ {l toks₁ B toks₂ T′ r′} → ParsesFuncProdG toks₁ B toks₂ → BackTF ParsesFuncSumTailG (fSum l B) toks₂ T′ r′
            → BackTF ParsesFuncSumTailG l (P.TPlus ∷ toks₁) T′ r′

  fk₁ (a , rest , dA , ha , er) = fK a , rest , pfa-k dA , trans (hF-k a) (cong S.fK ha) , er
  fparen₁ (f , rest , dF , hf , er) = fparen₂ dF hf (peel refl er)
  fparen₂ {f = f} dF hf (rest′ , refl , er) = f , rest′ , pfa-paren dF refl , hf , er
  fprod₁ (a , toks₁ , dA , ha , e₁) dT = fprod₂ dA (fptail← dT a toks₁ ha e₁)
  fprod₂ dA (T , rest , dT , hT , er) = T , rest , pfp-mk dA dT , hT , er
  fpstar₁ {l = l} hl (B , toks₂ , dB , hB , e₂) dT = fpstar₂ dB (fptail← dT (fProd l B) toks₂ (trans (hF-prod l B) (cong₂ S.fProd hl hB)) e₂)
  fpstar₂ dB (T , rest , dT , hT , er) = T , rest , pfpt-star refl dB dT , hT , er
  fsum₁ (a , toks₁ , dA , ha , e₁) dT = fsum₂ dA (fstail← dT a toks₁ ha e₁)
  fsum₂ dA (T , rest , dT , hT , er) = T , rest , pfs-mk dA dT , hT , er
  fsplus₁ {l = l} hl (B , toks₂ , dB , hB , e₂) dT = fsplus₂ dB (fstail← dT (fSum l B) toks₂ (trans (hF-sum l B) (cong₂ S.fSum hl hB)) e₂)
  fsplus₂ dB (T , rest , dT , hT , er) = T , rest , pfst-plus refl dB dT , hT , er

  fatom← f-id toks e = step (λ x → BackF ParsesFuncAtomG x S.fId _) refl e (λ {toks′} e′ → fId , toks′ , pfa-id toks′ , hF-id , e′)
  fatom← (f-k dA) toks e = step (λ x → BackF ParsesFuncAtomG x _ _) refl e (λ {toks′} e′ → fk₁ (atom← dA toks′ e′))
  fatom← (f-paren dF) toks e = step (λ x → BackF ParsesFuncAtomG x _ _) refl e (λ {toks′} e′ → fparen₁ (fsum← dF toks′ e′))

  fprod← (fprod dA dT) toks e = fprod₁ (fatom← dA toks e) dT

  fptail← (fprod-done n) l toks refl refl = l , toks , pfpt-done (star-false← toks n) , refl , refl
  fptail← (fprod-star dB dT) l toks hl e =
    step (λ x → BackTF ParsesFuncProdTailG l x _ _) refl e (λ {toks′} e′ → fpstar₁ hl (fatom← dB toks′ e′) dT)

  fsum← (fsum dA dT) toks e = fsum₁ (fprod← dA toks e) dT

  fstail← (fsum-done n) l toks refl refl = l , toks , pfst-done (plus-false← toks n) , refl , refl
  fstail← (fsum-plus dB dT) l toks hl e =
    step (λ x → BackTF ParsesFuncSumTailG l x _ _) refl e (λ {toks′} e′ → fsplus₁ hl (fprod← dB toks′ e′) dT)
