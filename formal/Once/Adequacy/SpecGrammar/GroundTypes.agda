-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.GroundTypes — the compiler's ground type
-- grammar (`Once.Parser.TypeRelation`, read into its `Type`) against the
-- Spec's (`Types`, over an algebra with no extra atoms).
--
-- Instances: an annotation (`Annot`, read by `toTy`) and the body of a type
-- alias (`AliasType`, read by `toPolyG`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.GroundTypes where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

import Once.Lang.Type.Grade as LG
import Once.Spec.Grade as SG
open import Once.Lang.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; Functor; K; Id; _⊕_; _⊗_; μ-type; ν-type)
open import Once.Spec.Surface.Lexing using (Token; TRParen)
open import Once.Spec.Surface.Grammar using (TypeAlg; module Types; NoExtra; module Annot; module AliasType; GradeToken; g0; g1; gw)
import Once.Spec.Type as ST
import Once.Spec.Surface.Syntax as SS
import Once.Parser.Token as P
open import Once.Parser.TypeRelation
open import Once.Adequacy.SpecGrammar.Tokens using (forget; step; peel)
open import Once.Adequacy.SpecGrammar.TypeHeads
  using (notStar→TStar; notStar←; notPlus→TPlus; notPlus←;
         notArrow→TArrow; notArrow→TCaret0; notArrow→TCaret1; notArrow→TCaretW; notArrow←)
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; toTy; toFun; toPolyG; toPolyGF)
open import Once.Adequacy.SpecGrammar.SigTypes using (writtenS)

private
  F : List P.Token → List Token
  F = map forget

module _ {R′ RF′ : Set} (salg : TypeAlg R′ RF′) where
  private module S = TypeAlg salg

  record HomG (h : Type → R′) (hF : Functor → RF′) : Set where
    field
      h-unit  : h Unit ≡ S.aUnit
      h-void  : h Void ≡ S.aVoid
      h-int   : h Int ≡ S.aInt
      h-float : h Float ≡ S.aFloat
      h-prod  : ∀ a b → h (a * b) ≡ S.aProd (h a) (h b)
      h-sum   : ∀ a b → h (a + b) ≡ S.aSum (h a) (h b)
      h-eff   : ∀ a b → h (a ⇒[ LG.mk-kind LG.Many LG.eff ] b) ≡ S.aEff (h a) (h b)
      h-act   : ∀ a b → h (a ⇒[ LG.mk-kind LG.Many LG.act ] b) ≡ S.aAct (h a) (h b)
      h-arrow : ∀ q a b → h (a ⇒[ LG.mk-kind q LG.pure ] b) ≡ S.aArrow (qS q) (h a) (h b)
      h-mu    : ∀ f → h (μ-type f) ≡ S.aMu (hF f)
      h-nu    : ∀ f π → h (ν-type f π) ≡ S.aNu (πS π) (hF f)
      hF-k    : ∀ a → hF (K a) ≡ S.fK (h a)
      hF-id   : hF Id ≡ S.fId
      hF-sum  : ∀ f g → hF (f ⊕ g) ≡ S.fSum (hF f) (hF g)
      hF-prod : ∀ f g → hF (f ⊗ g) ≡ S.fProd (hF f) (hF g)
      no-extra : ∀ {ts a r} → ¬ S.Extra ts a r

module Bridge {R′ RF′ : Set} (salg : TypeAlg R′ RF′) (h : Type → R′) (hF : Functor → RF′) (hom : HomG salg h hF) where
  private module S = TypeAlg salg
  open Types salg hiding (ParsesAtom; ParsesProd; ParsesProdTail; ParsesSum; ParsesSumTail; ParsesType; ParsesArrowTail)
  open HomG hom

  ----------------------------------------------------------------------
  -- The compiler's derivation gives the Spec's
  ----------------------------------------------------------------------

  atom→   : ∀ {toks a rest} → ParsesAtom toks a rest → Types.ParsesAtom salg (F toks) (h a) (F rest)
  prod→   : ∀ {toks a rest} → ParsesProd toks a rest → Types.ParsesProd salg (F toks) (h a) (F rest)
  ptail→  : ∀ {l toks a rest} → ParsesProdTail l toks a rest → Types.ParsesProdTail salg (h l) (F toks) (h a) (F rest)
  sum→    : ∀ {toks a rest} → ParsesSum toks a rest → Types.ParsesSum salg (F toks) (h a) (F rest)
  stail→  : ∀ {l toks a rest} → ParsesSumTail l toks a rest → Types.ParsesSumTail salg (h l) (F toks) (h a) (F rest)
  type→   : ∀ {toks a rest} → ParsesType toks a rest → Types.ParsesType salg (F toks) (h a) (F rest)
  atail→  : ∀ {l toks a rest} → ParsesArrowTail l toks a rest → Types.ParsesArrowTail salg (h l) (F toks) (h a) (F rest)
  fatom→  : ∀ {toks f rest} → ParsesFunctorAtom toks f rest → Types.ParsesFunAtom salg (F toks) (hF f) (F rest)
  fprod→  : ∀ {toks f rest} → ParsesFunctorProd toks f rest → Types.ParsesFunProd salg (F toks) (hF f) (F rest)
  fptail→ : ∀ {l toks f rest} → ParsesFunctorProdTail l toks f rest → Types.ParsesFunProdTail salg (hF l) (F toks) (hF f) (F rest)
  fsum→   : ∀ {toks f rest} → ParsesFunctorSum toks f rest → Types.ParsesFunSum salg (F toks) (hF f) (F rest)
  fstail→ : ∀ {l toks f rest} → ParsesFunctorSumTail l toks f rest → Types.ParsesFunSumTail salg (hF l) (F toks) (hF f) (F rest)

  private
    atomAt : ∀ {ts r x y} → x ≡ y → Types.ParsesAtom salg ts x r → Types.ParsesAtom salg ts y r
    atomAt e d = subst (λ z → Types.ParsesAtom salg _ z _) e d

    grade : ∀ q → GradeToken (forget (quantityTokenOf q)) (qS q)
    grade LG.Zero = g0
    grade LG.One  = g1
    grade LG.Many = gw

  atom→ (pa-unit _)  = atomAt (sym h-unit) a-unit
  atom→ (pa-void _)  = atomAt (sym h-void) a-void
  atom→ (pa-int _)   = atomAt (sym h-int) a-int
  atom→ (pa-float _) = atomAt (sym h-float) a-float
  atom→ (pa-eff dA dB) = atomAt (sym (h-eff _ _)) (a-eff (atom→ dA) (atom→ dB))
  atom→ (pa-act dA dB) = atomAt (sym (h-act _ _)) (a-act (atom→ dA) (atom→ dB))
  atom→ (pa-io dA) = atomAt (sym (trans (h-eff _ _) (cong (λ x → S.aEff x _) h-unit))) (a-io (atom→ dA))
  atom→ (pa-paren dT refl) = a-paren (type→ dT)
  atom→ (pa-mu dF) = atomAt (sym (h-mu _)) (a-mu (fsum→ dF))
  atom→ (pa-nu dF) = atomAt (sym (h-nu _ _)) (a-nu (fsum→ dF))
  atom→ (pa-nu-eff dF) = atomAt (sym (h-nu _ _)) (a-nu-eff (fsum→ dF))
  atom→ (pa-nu-act dF) = atomAt (sym (h-nu _ _)) (a-nu-act (fsum→ dF))

  prod→ (pp-mk dA dT) = prod (atom→ dA) (ptail→ dT)

  ptail→ {toks = toks} (ppt-done n) = prod-done (notStar→TStar toks n)
  ptail→ (ppt-star dB dT) = prod-star (atom→ dB) (subst (λ z → Types.ParsesProdTail salg z _ _ _) (h-prod _ _) (ptail→ dT))

  sum→ (ps-mk dA dT) = sum (prod→ dA) (stail→ dT)

  stail→ {toks = toks} (pst-done n) = sum-done (notPlus→TPlus toks n)
  stail→ (pst-plus dB dT) = sum-plus (prod→ dB) (subst (λ z → Types.ParsesSumTail salg z _ _ _) (h-sum _ _) (stail→ dT))

  type→ (pt-mk dS dA) = type (sum→ dS) (atail→ dA)

  atail→ {toks = toks} (pat-done n) =
    arrow-done (notArrow→TArrow toks n) (notArrow→TCaret0 toks n) (notArrow→TCaret1 toks n) (notArrow→TCaretW toks n)
  atail→ (pat-arrow-g {q = q} dT) =
    subst (λ z → Types.ParsesArrowTail salg _ _ z _) (sym (h-arrow _ _ _)) (arrow-grade (grade q) (type→ dT))
  atail→ (pat-arrow dT) = subst (λ z → Types.ParsesArrowTail salg _ _ z _) (sym (h-arrow _ _ _)) (arrow (type→ dT))

  fatom→ (pfa-id _) = subst (λ z → Types.ParsesFunAtom salg _ z _) (sym hF-id) f-id
  fatom→ (pfa-k dA) = subst (λ z → Types.ParsesFunAtom salg _ z _) (sym (hF-k _)) (f-k (atom→ dA))
  fatom→ (pfa-paren dF refl) = f-paren (fsum→ dF)

  fprod→ (pfp-mk dA dT) = fprod (fatom→ dA) (fptail→ dT)

  fptail→ {toks = toks} (pfpt-done n) = fprod-done (notStar→TStar toks n)
  fptail→ (pfpt-star dB dT) = fprod-star (fatom→ dB) (subst (λ z → Types.ParsesFunProdTail salg z _ _ _) (hF-prod _ _) (fptail→ dT))

  fsum→ (pfs-mk dA dT) = fsum (fprod→ dA) (fstail→ dT)

  fstail→ {toks = toks} (pfst-done n) = fsum-done (notPlus→TPlus toks n)
  fstail→ (pfst-plus dB dT) = fsum-plus (fprod→ dB) (subst (λ z → Types.ParsesFunSumTail salg z _ _ _) (hF-sum _ _) (fstail→ dT))

  ----------------------------------------------------------------------
  -- The Spec's derivation comes from the compiler's
  ----------------------------------------------------------------------

  Back : (List P.Token → Type → List P.Token → Set) → List P.Token → R′ → List Token → Set
  Back Rel toks a′ r′ = Σ[ a ∈ Type ] Σ[ rest ∈ List P.Token ] (Rel toks a rest × h a ≡ a′ × F rest ≡ r′)

  BackF : (List P.Token → Functor → List P.Token → Set) → List P.Token → RF′ → List Token → Set
  BackF Rel toks f′ r′ = Σ[ f ∈ Functor ] Σ[ rest ∈ List P.Token ] (Rel toks f rest × hF f ≡ f′ × F rest ≡ r′)

  BackT : (Type → List P.Token → Type → List P.Token → Set) → Type → List P.Token → R′ → List Token → Set
  BackT Rel l toks a′ r′ = Σ[ a ∈ Type ] Σ[ rest ∈ List P.Token ] (Rel l toks a rest × h a ≡ a′ × F rest ≡ r′)

  BackTF : (Functor → List P.Token → Functor → List P.Token → Set) → Functor → List P.Token → RF′ → List Token → Set
  BackTF Rel l toks f′ r′ = Σ[ f ∈ Functor ] Σ[ rest ∈ List P.Token ] (Rel l toks f rest × hF f ≡ f′ × F rest ≡ r′)

  atom←   : ∀ {ts a′ r′} → Types.ParsesAtom salg ts a′ r′ → ∀ toks → F toks ≡ ts → Back ParsesAtom toks a′ r′
  prod←   : ∀ {ts a′ r′} → Types.ParsesProd salg ts a′ r′ → ∀ toks → F toks ≡ ts → Back ParsesProd toks a′ r′
  ptail←  : ∀ {l′ ts a′ r′} → Types.ParsesProdTail salg l′ ts a′ r′ → ∀ l toks → h l ≡ l′ → F toks ≡ ts → BackT ParsesProdTail l toks a′ r′
  sum←    : ∀ {ts a′ r′} → Types.ParsesSum salg ts a′ r′ → ∀ toks → F toks ≡ ts → Back ParsesSum toks a′ r′
  stail←  : ∀ {l′ ts a′ r′} → Types.ParsesSumTail salg l′ ts a′ r′ → ∀ l toks → h l ≡ l′ → F toks ≡ ts → BackT ParsesSumTail l toks a′ r′
  type←   : ∀ {ts a′ r′} → Types.ParsesType salg ts a′ r′ → ∀ toks → F toks ≡ ts → Back ParsesType toks a′ r′
  atail←  : ∀ {l′ ts a′ r′} → Types.ParsesArrowTail salg l′ ts a′ r′ → ∀ l toks → h l ≡ l′ → F toks ≡ ts → BackT ParsesArrowTail l toks a′ r′
  fatom←  : ∀ {ts f′ r′} → Types.ParsesFunAtom salg ts f′ r′ → ∀ toks → F toks ≡ ts → BackF ParsesFunctorAtom toks f′ r′
  fprod←  : ∀ {ts f′ r′} → Types.ParsesFunProd salg ts f′ r′ → ∀ toks → F toks ≡ ts → BackF ParsesFunctorProd toks f′ r′
  fptail← : ∀ {l′ ts f′ r′} → Types.ParsesFunProdTail salg l′ ts f′ r′ → ∀ l toks → hF l ≡ l′ → F toks ≡ ts → BackTF ParsesFunctorProdTail l toks f′ r′
  fsum←   : ∀ {ts f′ r′} → Types.ParsesFunSum salg ts f′ r′ → ∀ toks → F toks ≡ ts → BackF ParsesFunctorSum toks f′ r′
  fstail← : ∀ {l′ ts f′ r′} → Types.ParsesFunSumTail salg l′ ts f′ r′ → ∀ l toks → hF l ≡ l′ → F toks ≡ ts → BackTF ParsesFunctorSumTail l toks f′ r′

  private
    eff₁ : ∀ {toks₁ A′ ts₂ B′ r′} → Back ParsesAtom toks₁ A′ ts₂ → Types.ParsesAtom salg ts₂ B′ r′
         → Back ParsesAtom (P.TWord "Eff" ∷ toks₁) (S.aEff A′ B′) r′
    eff₂ : ∀ {toks₁ A toks₂ A′ B′ r′} → ParsesAtom toks₁ A toks₂ → h A ≡ A′ → Back ParsesAtom toks₂ B′ r′
         → Back ParsesAtom (P.TWord "Eff" ∷ toks₁) (S.aEff A′ B′) r′
    act₁ : ∀ {toks₁ A′ ts₂ B′ r′} → Back ParsesAtom toks₁ A′ ts₂ → Types.ParsesAtom salg ts₂ B′ r′
         → Back ParsesAtom (P.TWord "Act" ∷ toks₁) (S.aAct A′ B′) r′
    act₂ : ∀ {toks₁ A toks₂ A′ B′ r′} → ParsesAtom toks₁ A toks₂ → h A ≡ A′ → Back ParsesAtom toks₂ B′ r′
         → Back ParsesAtom (P.TWord "Act" ∷ toks₁) (S.aAct A′ B′) r′
    io₁  : ∀ {toks₁ A′ r′} → Back ParsesAtom toks₁ A′ r′ → Back ParsesAtom (P.TWord "IO" ∷ toks₁) (S.aEff S.aUnit A′) r′
    mu₁  : ∀ {toks₁ F′ r′} → BackF ParsesFunctorSum toks₁ F′ r′ → Back ParsesAtom (P.TWord "Mu" ∷ toks₁) (S.aMu F′) r′
    nu₁  : ∀ {toks₁ F′ r′} → BackF ParsesFunctorSum toks₁ F′ r′ → Back ParsesAtom (P.TWord "Nu" ∷ toks₁) (S.aNu SG.pure F′) r′
    nueff₁ : ∀ {toks₁ F′ r′} → BackF ParsesFunctorSum toks₁ F′ (TRParen ∷ r′)
           → Back ParsesAtom (P.TWord "Nu" ∷ P.TLParen ∷ P.TWord "Eff" ∷ toks₁) (S.aNu SG.eff F′) r′
    nueff₂ : ∀ {toks₁ f rest F′ r′} → ParsesFunctorSum toks₁ f rest → hF f ≡ F′
           → Σ[ rest′ ∈ List P.Token ] (rest ≡ P.TRParen ∷ rest′ × F rest′ ≡ r′)
           → Back ParsesAtom (P.TWord "Nu" ∷ P.TLParen ∷ P.TWord "Eff" ∷ toks₁) (S.aNu SG.eff F′) r′
    nuact₁ : ∀ {toks₁ F′ r′} → BackF ParsesFunctorSum toks₁ F′ (TRParen ∷ r′)
           → Back ParsesAtom (P.TWord "Nu" ∷ P.TLParen ∷ P.TWord "Act" ∷ toks₁) (S.aNu SG.act F′) r′
    nuact₂ : ∀ {toks₁ f rest F′ r′} → ParsesFunctorSum toks₁ f rest → hF f ≡ F′
           → Σ[ rest′ ∈ List P.Token ] (rest ≡ P.TRParen ∷ rest′ × F rest′ ≡ r′)
           → Back ParsesAtom (P.TWord "Nu" ∷ P.TLParen ∷ P.TWord "Act" ∷ toks₁) (S.aNu SG.act F′) r′
    paren₁ : ∀ {toks₁ A′ r′} → Back ParsesType toks₁ A′ (TRParen ∷ r′) → Back ParsesAtom (P.TLParen ∷ toks₁) A′ r′
    paren₂ : ∀ {toks₁ a rest A′ r′} → ParsesType toks₁ a rest → h a ≡ A′
           → Σ[ rest′ ∈ List P.Token ] (rest ≡ P.TRParen ∷ rest′ × F rest′ ≡ r′)
           → Back ParsesAtom (P.TLParen ∷ toks₁) A′ r′

  eff₁ (A , toks₂ , dA , hA , e₂) dB = eff₂ dA hA (atom← dB toks₂ e₂)
  eff₂ {A = A} dA hA (B , rest , dB , hB , er) = _ , rest , pa-eff dA dB , trans (h-eff A B) (cong₂ S.aEff hA hB) , er
  act₁ (A , toks₂ , dA , hA , e₂) dB = act₂ dA hA (atom← dB toks₂ e₂)
  act₂ {A = A} dA hA (B , rest , dB , hB , er) = _ , rest , pa-act dA dB , trans (h-act A B) (cong₂ S.aAct hA hB) , er
  io₁ (A , rest , dA , hA , er) = _ , rest , pa-io dA , trans (h-eff Unit A) (cong₂ S.aEff h-unit hA) , er
  mu₁ (f , rest , dF , hf , er) = _ , rest , pa-mu dF , trans (h-mu f) (cong S.aMu hf) , er
  nu₁ (f , rest , dF , hf , er) = _ , rest , pa-nu dF , trans (h-nu f LG.pure) (cong (S.aNu SG.pure) hf) , er
  nueff₁ (f , rest , dF , hf , er) = nueff₂ dF hf (peel refl er)
  nueff₂ {f = f} dF hf (rest′ , refl , er) = _ , rest′ , pa-nu-eff dF , trans (h-nu f LG.eff) (cong (S.aNu SG.eff) hf) , er
  nuact₁ (f , rest , dF , hf , er) = nuact₂ dF hf (peel refl er)
  nuact₂ {f = f} dF hf (rest′ , refl , er) = _ , rest′ , pa-nu-act dF , trans (h-nu f LG.act) (cong (S.aNu SG.act) hf) , er
  paren₁ (a , rest , dT , ha , er) = paren₂ dT ha (peel refl er)
  paren₂ dT ha (rest′ , refl , er) = _ , rest′ , pa-paren dT refl , ha , er

  atom← a-unit toks e = step (λ x → Back ParsesAtom x S.aUnit _) refl e (λ {toks′} e′ → Unit , toks′ , pa-unit toks′ , h-unit , e′)
  atom← a-void toks e = step (λ x → Back ParsesAtom x S.aVoid _) refl e (λ {toks′} e′ → Void , toks′ , pa-void toks′ , h-void , e′)
  atom← a-int toks e = step (λ x → Back ParsesAtom x S.aInt _) refl e (λ {toks′} e′ → Int , toks′ , pa-int toks′ , h-int , e′)
  atom← a-float toks e = step (λ x → Back ParsesAtom x S.aFloat _) refl e (λ {toks′} e′ → Float , toks′ , pa-float toks′ , h-float , e′)
  atom← (a-eff dA dB) toks e = step (λ x → Back ParsesAtom x _ _) refl e (λ {toks′} e′ → eff₁ (atom← dA toks′ e′) dB)
  atom← (a-act dA dB) toks e = step (λ x → Back ParsesAtom x _ _) refl e (λ {toks′} e′ → act₁ (atom← dA toks′ e′) dB)
  atom← (a-io dA) toks e = step (λ x → Back ParsesAtom x _ _) refl e (λ {toks′} e′ → io₁ (atom← dA toks′ e′))
  atom← (a-mu dF) toks e = step (λ x → Back ParsesAtom x _ _) refl e (λ {toks′} e′ → mu₁ (fsum← dF toks′ e′))
  atom← (a-nu dF) toks e = step (λ x → Back ParsesAtom x _ _) refl e (λ {toks′} e′ → nu₁ (fsum← dF toks′ e′))
  atom← (a-nu-eff dF) toks e =
    step (λ x → Back ParsesAtom x _ _) refl e (λ e₁ →
    step (λ x → Back ParsesAtom (P.TWord "Nu" ∷ x) _ _) refl e₁ (λ e₂ →
    step (λ x → Back ParsesAtom (P.TWord "Nu" ∷ P.TLParen ∷ x) _ _) refl e₂ (λ {toks′} e₃ →
    nueff₁ (fsum← dF toks′ e₃))))
  atom← (a-nu-act dF) toks e =
    step (λ x → Back ParsesAtom x _ _) refl e (λ e₁ →
    step (λ x → Back ParsesAtom (P.TWord "Nu" ∷ x) _ _) refl e₁ (λ e₂ →
    step (λ x → Back ParsesAtom (P.TWord "Nu" ∷ P.TLParen ∷ x) _ _) refl e₂ (λ {toks′} e₃ →
    nuact₁ (fsum← dF toks′ e₃))))
  atom← (a-extra ex) toks e = ⊥-elim (no-extra ex)
  atom← (a-paren dT) toks e = step (λ x → Back ParsesAtom x _ _) refl e (λ {toks′} e′ → paren₁ (type← dT toks′ e′))

  private
    prod₁ : ∀ {toks a′ ts₁ T′ r′} → Back ParsesAtom toks a′ ts₁ → Types.ParsesProdTail salg a′ ts₁ T′ r′ → Back ParsesProd toks T′ r′
    prod₂ : ∀ {toks a toks₁ T′ r′} → ParsesAtom toks a toks₁ → BackT ParsesProdTail a toks₁ T′ r′ → Back ParsesProd toks T′ r′
    pstar₁ : ∀ {l toks₁ B′ ts₂ l′ T′ r′} → h l ≡ l′ → Back ParsesAtom toks₁ B′ ts₂ → Types.ParsesProdTail salg (S.aProd l′ B′) ts₂ T′ r′
           → BackT ParsesProdTail l (P.TStar ∷ toks₁) T′ r′
    pstar₂ : ∀ {l toks₁ B toks₂ T′ r′} → ParsesAtom toks₁ B toks₂ → BackT ParsesProdTail (l * B) toks₂ T′ r′
           → BackT ParsesProdTail l (P.TStar ∷ toks₁) T′ r′

  prod₁ (a , toks₁ , dA , ha , e₁) dT = prod₂ dA (ptail← dT a toks₁ ha e₁)
  prod₂ dA (T , rest , dT , hT , er) = T , rest , pp-mk dA dT , hT , er
  pstar₁ {l = l} hl (B , toks₂ , dB , hB , e₂) dT = pstar₂ dB (ptail← dT (l * B) toks₂ (trans (h-prod l B) (cong₂ S.aProd hl hB)) e₂)
  pstar₂ dB (T , rest , dT , hT , er) = T , rest , ppt-star dB dT , hT , er

  prod← (prod dA dT) toks e = prod₁ (atom← dA toks e) dT

  ptail← (prod-done n) l toks refl refl = l , toks , ppt-done (notStar← toks n) , refl , refl
  ptail← (prod-star dB dT) l toks hl e =
    step (λ x → BackT ParsesProdTail l x _ _) refl e (λ {toks′} e′ → pstar₁ hl (atom← dB toks′ e′) dT)

  private
    sum₁ : ∀ {toks a′ ts₁ T′ r′} → Back ParsesProd toks a′ ts₁ → Types.ParsesSumTail salg a′ ts₁ T′ r′ → Back ParsesSum toks T′ r′
    sum₂ : ∀ {toks a toks₁ T′ r′} → ParsesProd toks a toks₁ → BackT ParsesSumTail a toks₁ T′ r′ → Back ParsesSum toks T′ r′
    splus₁ : ∀ {l toks₁ B′ ts₂ l′ T′ r′} → h l ≡ l′ → Back ParsesProd toks₁ B′ ts₂ → Types.ParsesSumTail salg (S.aSum l′ B′) ts₂ T′ r′
           → BackT ParsesSumTail l (P.TPlus ∷ toks₁) T′ r′
    splus₂ : ∀ {l toks₁ B toks₂ T′ r′} → ParsesProd toks₁ B toks₂ → BackT ParsesSumTail (l + B) toks₂ T′ r′
           → BackT ParsesSumTail l (P.TPlus ∷ toks₁) T′ r′

  sum₁ (a , toks₁ , dA , ha , e₁) dT = sum₂ dA (stail← dT a toks₁ ha e₁)
  sum₂ dA (T , rest , dT , hT , er) = T , rest , ps-mk dA dT , hT , er
  splus₁ {l = l} hl (B , toks₂ , dB , hB , e₂) dT = splus₂ dB (stail← dT (l + B) toks₂ (trans (h-sum l B) (cong₂ S.aSum hl hB)) e₂)
  splus₂ dB (T , rest , dT , hT , er) = T , rest , pst-plus dB dT , hT , er

  sum← (sum dA dT) toks e = sum₁ (prod← dA toks e) dT

  stail← (sum-done n) l toks refl refl = l , toks , pst-done (notPlus← toks n) , refl , refl
  stail← (sum-plus dB dT) l toks hl e =
    step (λ x → BackT ParsesSumTail l x _ _) refl e (λ {toks′} e′ → splus₁ hl (prod← dB toks′ e′) dT)

  private
    type₁ : ∀ {toks a′ ts₁ T′ r′} → Back ParsesSum toks a′ ts₁ → Types.ParsesArrowTail salg a′ ts₁ T′ r′ → Back ParsesType toks T′ r′
    type₂ : ∀ {toks a toks₁ T′ r′} → ParsesSum toks a toks₁ → BackT ParsesArrowTail a toks₁ T′ r′ → Back ParsesType toks T′ r′
    graded : ∀ {l toks₁ B′ l′ r′} (q : LG.Quantity) → h l ≡ l′ → Back ParsesType toks₁ B′ r′
           → BackT ParsesArrowTail l (quantityTokenOf q ∷ P.TArrow ∷ toks₁) (S.aArrow (qS q) l′ B′) r′
    plain : ∀ {l toks₁ B′ l′ r′} → h l ≡ l′ → Back ParsesType toks₁ B′ r′
          → BackT ParsesArrowTail l (P.TArrow ∷ toks₁) (S.aArrow SG.Many l′ B′) r′

  type₁ (a , toks₁ , dS , ha , e₁) dA = type₂ dS (atail← dA a toks₁ ha e₁)
  type₂ dS (T , rest , dA , hT , er) = T , rest , pt-mk dS dA , hT , er

  type← (type dS dA) toks e = type₁ (sum← dS toks e) dA

  graded {l = l} q hl (B , rest , dB , hB , er) =
    _ , rest , pat-arrow-g {q = q} dB , trans (h-arrow q l B) (cong₂ (S.aArrow (qS q)) hl hB) , er
  plain {l = l} hl (B , rest , dB , hB , er) =
    _ , rest , pat-arrow dB , trans (h-arrow LG.Many l B) (cong₂ (S.aArrow SG.Many) hl hB) , er

  atail← (arrow-done a b c d) l toks refl refl = l , toks , pat-done (notArrow← toks a b c d) , refl , refl
  atail← (arrow-grade g0 dT) l toks hl e =
    step (λ x → BackT ParsesArrowTail l x _ _) refl e (λ e₁ →
    step (λ x → BackT ParsesArrowTail l (P.TCaret0 ∷ x) _ _) refl e₁ (λ {toks′} e₂ →
    graded LG.Zero hl (type← dT toks′ e₂)))
  atail← (arrow-grade g1 dT) l toks hl e =
    step (λ x → BackT ParsesArrowTail l x _ _) refl e (λ e₁ →
    step (λ x → BackT ParsesArrowTail l (P.TCaret1 ∷ x) _ _) refl e₁ (λ {toks′} e₂ →
    graded LG.One hl (type← dT toks′ e₂)))
  atail← (arrow-grade gw dT) l toks hl e =
    step (λ x → BackT ParsesArrowTail l x _ _) refl e (λ e₁ →
    step (λ x → BackT ParsesArrowTail l (P.TCaretW ∷ x) _ _) refl e₁ (λ {toks′} e₂ →
    graded LG.Many hl (type← dT toks′ e₂)))
  atail← (arrow dT) l toks hl e =
    step (λ x → BackT ParsesArrowTail l x _ _) refl e (λ {toks′} e′ → plain hl (type← dT toks′ e′))

  private
    fk₁ : ∀ {toks₁ A′ r′} → Back ParsesAtom toks₁ A′ r′ → BackF ParsesFunctorAtom (P.TWord "K" ∷ toks₁) (S.fK A′) r′
    fparen₁ : ∀ {toks₁ F′ r′} → BackF ParsesFunctorSum toks₁ F′ (TRParen ∷ r′) → BackF ParsesFunctorAtom (P.TLParen ∷ toks₁) F′ r′
    fparen₂ : ∀ {toks₁ f rest F′ r′} → ParsesFunctorSum toks₁ f rest → hF f ≡ F′
            → Σ[ rest′ ∈ List P.Token ] (rest ≡ P.TRParen ∷ rest′ × F rest′ ≡ r′)
            → BackF ParsesFunctorAtom (P.TLParen ∷ toks₁) F′ r′
    fprod₁ : ∀ {toks a′ ts₁ T′ r′} → BackF ParsesFunctorAtom toks a′ ts₁ → Types.ParsesFunProdTail salg a′ ts₁ T′ r′ → BackF ParsesFunctorProd toks T′ r′
    fprod₂ : ∀ {toks a toks₁ T′ r′} → ParsesFunctorAtom toks a toks₁ → BackTF ParsesFunctorProdTail a toks₁ T′ r′ → BackF ParsesFunctorProd toks T′ r′
    fpstar₁ : ∀ {l toks₁ B′ ts₂ l′ T′ r′} → hF l ≡ l′ → BackF ParsesFunctorAtom toks₁ B′ ts₂ → Types.ParsesFunProdTail salg (S.fProd l′ B′) ts₂ T′ r′
            → BackTF ParsesFunctorProdTail l (P.TStar ∷ toks₁) T′ r′
    fpstar₂ : ∀ {l toks₁ B toks₂ T′ r′} → ParsesFunctorAtom toks₁ B toks₂ → BackTF ParsesFunctorProdTail (l ⊗ B) toks₂ T′ r′
            → BackTF ParsesFunctorProdTail l (P.TStar ∷ toks₁) T′ r′
    fsum₁ : ∀ {toks a′ ts₁ T′ r′} → BackF ParsesFunctorProd toks a′ ts₁ → Types.ParsesFunSumTail salg a′ ts₁ T′ r′ → BackF ParsesFunctorSum toks T′ r′
    fsum₂ : ∀ {toks a toks₁ T′ r′} → ParsesFunctorProd toks a toks₁ → BackTF ParsesFunctorSumTail a toks₁ T′ r′ → BackF ParsesFunctorSum toks T′ r′
    fsplus₁ : ∀ {l toks₁ B′ ts₂ l′ T′ r′} → hF l ≡ l′ → BackF ParsesFunctorProd toks₁ B′ ts₂ → Types.ParsesFunSumTail salg (S.fSum l′ B′) ts₂ T′ r′
            → BackTF ParsesFunctorSumTail l (P.TPlus ∷ toks₁) T′ r′
    fsplus₂ : ∀ {l toks₁ B toks₂ T′ r′} → ParsesFunctorProd toks₁ B toks₂ → BackTF ParsesFunctorSumTail (l ⊕ B) toks₂ T′ r′
            → BackTF ParsesFunctorSumTail l (P.TPlus ∷ toks₁) T′ r′

  fk₁ (a , rest , dA , ha , er) = _ , rest , pfa-k dA , trans (hF-k a) (cong S.fK ha) , er
  fparen₁ (f , rest , dF , hf , er) = fparen₂ dF hf (peel refl er)
  fparen₂ dF hf (rest′ , refl , er) = _ , rest′ , pfa-paren dF refl , hf , er
  fprod₁ (a , toks₁ , dA , ha , e₁) dT = fprod₂ dA (fptail← dT a toks₁ ha e₁)
  fprod₂ dA (T , rest , dT , hT , er) = T , rest , pfp-mk dA dT , hT , er
  fpstar₁ {l = l} hl (B , toks₂ , dB , hB , e₂) dT = fpstar₂ dB (fptail← dT (l ⊗ B) toks₂ (trans (hF-prod l B) (cong₂ S.fProd hl hB)) e₂)
  fpstar₂ dB (T , rest , dT , hT , er) = T , rest , pfpt-star dB dT , hT , er
  fsum₁ (a , toks₁ , dA , ha , e₁) dT = fsum₂ dA (fstail← dT a toks₁ ha e₁)
  fsum₂ dA (T , rest , dT , hT , er) = T , rest , pfs-mk dA dT , hT , er
  fsplus₁ {l = l} hl (B , toks₂ , dB , hB , e₂) dT = fsplus₂ dB (fstail← dT (l ⊕ B) toks₂ (trans (hF-sum l B) (cong₂ S.fSum hl hB)) e₂)
  fsplus₂ dB (T , rest , dT , hT , er) = T , rest , pfst-plus dB dT , hT , er

  fatom← f-id toks e = step (λ x → BackF ParsesFunctorAtom x S.fId _) refl e (λ {toks′} e′ → Id , toks′ , pfa-id toks′ , hF-id , e′)
  fatom← (f-k dA) toks e = step (λ x → BackF ParsesFunctorAtom x _ _) refl e (λ {toks′} e′ → fk₁ (atom← dA toks′ e′))
  fatom← (f-paren dF) toks e = step (λ x → BackF ParsesFunctorAtom x _ _) refl e (λ {toks′} e′ → fparen₁ (fsum← dF toks′ e′))

  fprod← (fprod dA dT) toks e = fprod₁ (fatom← dA toks e) dT

  fptail← (fprod-done n) l toks refl refl = l , toks , pfpt-done (notStar← toks n) , refl , refl
  fptail← (fprod-star dB dT) l toks hl e =
    step (λ x → BackTF ParsesFunctorProdTail l x _ _) refl e (λ {toks′} e′ → fpstar₁ hl (fatom← dB toks′ e′) dT)

  fsum← (fsum dA dT) toks e = fsum₁ (fprod← dA toks e) dT

  fstail← (fsum-done n) l toks refl refl = l , toks , pfst-done (notPlus← toks n) , refl , refl
  fstail← (fsum-plus dB dT) l toks hl e =
    step (λ x → BackTF ParsesFunctorSumTail l x _ _) refl e (λ {toks′} e′ → fsplus₁ hl (fprod← dB toks′ e′) dT)

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

-- The Spec's ground algebra (`Once.Spec.Surface.Grammar`'s, private there).
groundS : TypeAlg ST.Type (ST.Fun 0)
groundS = record
  { aUnit = ST.Unit ; aVoid = ST.Void ; aInt = ST.Int ; aFloat = ST.Float
  ; aProd = ST._*_ ; aSum = ST._+_
  ; aEff = λ A B → A ST.⇒[ SG.mk-kind SG.Many SG.eff ] B ; aAct = λ A B → A ST.⇒[ SG.mk-kind SG.Many SG.act ] B
  ; aArrow = λ q A B → A ST.⇒[ SG.mk-kind q SG.pure ] B ; aMu = ST.μ ; aNu = λ π F → ST.ν F π
  ; fK = ST.K ; fId = ST.Id ; fSum = ST._⊕_ ; fProd = ST._⊗_
  ; Extra = NoExtra }

homTy : HomG groundS toTy toFun
homTy = record
  { h-unit = refl ; h-void = refl ; h-int = refl ; h-float = refl
  ; h-prod = λ _ _ → refl ; h-sum = λ _ _ → refl ; h-eff = λ _ _ → refl ; h-act = λ _ _ → refl
  ; h-arrow = λ _ _ _ → refl ; h-mu = λ _ → refl ; h-nu = λ _ _ → refl
  ; hF-k = λ _ → refl ; hF-id = refl ; hF-sum = λ _ _ → refl ; hF-prod = λ _ _ → refl
  ; no-extra = λ () }

homAlias : HomG (writtenS NoExtra) toPolyG toPolyGF
homAlias = record
  { h-unit = refl ; h-void = refl ; h-int = refl ; h-float = refl
  ; h-prod = λ _ _ → refl ; h-sum = λ _ _ → refl ; h-eff = λ _ _ → refl ; h-act = λ _ _ → refl
  ; h-arrow = λ _ _ _ → refl ; h-mu = λ _ → refl ; h-nu = λ _ _ → refl
  ; hF-k = λ _ → refl ; hF-id = refl ; hF-sum = λ _ _ → refl ; hF-prod = λ _ _ → refl
  ; no-extra = λ () }

private
  module BA = Bridge groundS toTy toFun homTy
  module BL = Bridge (writtenS NoExtra) toPolyG toPolyGF homAlias

annot→ : ∀ {toks A rest} → ParsesType toks A rest → Annot.ParsesType (F toks) (toTy A) (F rest)
annot→ = BA.type→

annot← : ∀ {ts A′ r′} → Annot.ParsesType ts A′ r′ → ∀ toks → F toks ≡ ts
       → Σ[ A ∈ Type ] Σ[ rest ∈ List P.Token ] (ParsesType toks A rest × toTy A ≡ A′ × F rest ≡ r′)
annot← = BA.type←

alias→ : ∀ {toks A rest} → ParsesType toks A rest → AliasType.ParsesType (F toks) (toPolyG A) (F rest)
alias→ = BL.type→

alias← : ∀ {ts A′ r′} → AliasType.ParsesType ts A′ r′ → ∀ toks → F toks ≡ ts
       → Σ[ A ∈ Type ] Σ[ rest ∈ List P.Token ] (ParsesType toks A rest × toPolyG A ≡ A′ × F rest ≡ r′)
alias← = BL.type←
