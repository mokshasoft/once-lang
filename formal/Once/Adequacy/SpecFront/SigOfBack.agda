-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SigOfBack — the extractor reads the program's
-- signature the Spec reads (plan 0.121 `complete`; the converse of `SigOf`).
--
-- Each `signature` the Spec reads (`SignaturesOf`, `Imported`), well-formed,
-- is one the extractor reads (`SigBack.project-of`), at the same table type:
-- the module's own (`own-part←`), and its imports', owned by their paths
-- (`imp-part←`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.SigOfBack where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import Once.Parser as Parser
open import Once.Parser using (Entry; e-fun; e-poly; mkFunInfo)
open import Once.Parser.Module.Core using (Module; mkModule; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Spec.Surface.Syntax using (mkImport)
open import Once.Parser.Module.Resolve using (ModuleMap; sigsOf; importedAt; importedOf; expandPath)
open import Once.Adequacy.ResolveBridge using (lookupMod-complete)
import Once.Internal.Resolution as LR
open import Once.Internal.Module using (entrySig)
open import Once.Spec.Name using (canonical)
open import Once.Internal.Name using (showCanonical)
open import Once.Spec.Surface.Syntax using (RVar)
open import Once.Spec.Signature using (Signature; WellFormed; []; _∷_)
import Once.Spec.Surface.Syntax as S
import Once.Spec.Surface.Resolution as SR
open import Once.Spec.Surface.Program
  using (SignaturesOf; so-nil; so-sig; so-other; ns-tsig; ns-def; ns-alias; ns-import;
         Imported; im-nil; im-import; im-other; ni-sig; ni-tsig; ni-def; ni-alias)
open import Once.Internal.Core.Decl using (toISig)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-fundef; d-signature; d-alias; d-import)
open import Once.Adequacy.SpecFront.Extract using (XAlign; xa-nil; xa-pass; xa-mono; xa-poly; xa-nosig; xa-sig; IsSig; is-sig; imported-sigs; FFIFacts)
open import Once.Adequacy.SpecFront.SigBack using (project-of; decl-honest; declTy-concrete)
open import Once.Adequacy.SpecInterp using (declTy)
open import Once.Spec.Signature using (WellFormedDecl)
open import Once.Spec.Surface.Program using (DeclTypeOf)
open import Once.Adequacy.SpecFront.SigOf using (importedSigs-++; expands-of)
open import Once.Adequacy.SpecFront.ModRel using (ModRel; find)

------------------------------------------------------------------------
-- Lists of entries
------------------------------------------------------------------------

-- Two descriptions, one after the other.
xa-++ : ∀ {ds₁ ds₂ es₁ es₂} → XAlign ds₁ es₁ → XAlign ds₂ es₂ → XAlign (ds₁ ++ ds₂) (es₁ ++ es₂)
xa-++ xa-nil         x₂ = x₂
xa-++ (xa-pass p x)  x₂ = xa-pass p (xa-++ x x₂)
xa-++ (xa-mono r x)  x₂ = xa-mono r (xa-++ x x₂)
xa-++ (xa-poly r x)  x₂ = xa-poly r (xa-++ x x₂)
xa-++ (xa-nosig x)   x₂ = xa-nosig (xa-++ x x₂)
xa-++ (xa-sig p x)   x₂ = xa-sig p (xa-++ x x₂)

-- The signatures' entries: their table distributes.
sigs-table-++ : ∀ {sigs fs} → All IsSig sigs → XAlign sigs fs → ∀ es → entrySig (fs ++ es) ≡ entrySig fs ++ entrySig es
sigs-table-++ [] xa-nil es = refl
sigs-table-++ (is-sig ∷ a) (xa-pass () _)
sigs-table-++ (is-sig ∷ a) (xa-sig _ x)  es = cong (_ ∷_) (sigs-table-++ a x es)

toISig-++ : ∀ (Σ₁ Σ₂ : Signature) → toISig (Σ₁ ++ Σ₂) ≡ toISig Σ₁ ++ toISig Σ₂
toISig-++ []        Σ₂ = refl
toISig-++ (d ∷ Σ₁) Σ₂ = cong (_ ∷_) (toISig-++ Σ₁ Σ₂)

wf-++ : ∀ (Σ₁ : Signature) {Σ₂} → WellFormed (Σ₁ ++ Σ₂) → WellFormed Σ₁ × WellFormed Σ₂
wf-++ []       w       = [] , w
wf-++ (d ∷ Σ₁) (w ∷ ws) = let (w₁ , w₂) = wf-++ Σ₁ ws in w ∷ w₁ , w₂

private
  -- the module a path names is found once
  first-unique : ∀ {p : List String} {ds ds′} {mm : SR.ModuleMap} → SR.FirstAt p (S.mkModule ds) mm → SR.FirstAt p (S.mkModule ds′) mm → ds ≡ ds′
  first-unique SR.fa-here          SR.fa-here          = refl
  first-unique SR.fa-here          (SR.fa-there ne _)  = Data.Empty.⊥-elim (ne refl)
    where import Data.Empty
  first-unique (SR.fa-there ne _)  SR.fa-here          = Data.Empty.⊥-elim (ne refl)
    where import Data.Empty
  first-unique (SR.fa-there _ f)   (SR.fa-there _ f′)  = first-unique f f′

  expands-unique : ∀ {p p′ p″} → SR.Expands p p′ → SR.Expands p p″ → p′ ≡ p″
  expands-unique SR.ex-nil       SR.ex-nil       = refl
  expands-unique SR.ex-I         SR.ex-I         = refl
  expands-unique SR.ex-I         (SR.ex-other n) = Data.Empty.⊥-elim (n refl)
    where import Data.Empty
  expands-unique (SR.ex-other n) SR.ex-I         = Data.Empty.⊥-elim (n refl)
    where import Data.Empty
  expands-unique (SR.ex-other _) (SR.ex-other _) = refl

-- An FFI entry the Spec reads has the telescope's facts.
ffi-facts : ∀ {P} t {n b} → DeclTypeOf P t → WellFormedDecl t → FFIFacts (e-fun (mkFunInfo n (just (declTy t)) b true))
ffi-facts t dto w = refl , declTy t , refl , declTy-concrete t , decl-honest dto w

all-++ : ∀ {A : Set} {P : A → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
all-++ []       q = q
all-++ (p ∷ ps) q = p ∷ all-++ ps q

------------------------------------------------------------------------
-- The module's own signatures
------------------------------------------------------------------------

own-part← : ∀ {dsU ds′ Σ₀} → Pointwise DEmb dsU ds′ → SignaturesOf [] ds′ Σ₀ → WellFormed Σ₀
          → Σ[ fs ∈ List Entry ] XAlign (Parser.ownSigs dsU) fs × (toISig Σ₀ ≡ entrySig fs) × All FFIFacts fs
own-part← [] so-nil [] = [] , xa-nil , refl , []
own-part← (d-signature {x = x} {A = A} ∷ pw) (so-sig {t = t} dto so) (w ∷ ws) =
  let (fs , xa , ti , fa) = own-part← pw so ws
  in _ , xa-sig (project-of x A dto w) xa , cong (_ ∷_) ti , ffi-facts t {n = x} {b = RVar x} dto w ∷ fa
own-part← (d-typesig ∷ pw)  (so-other ns-tsig so)   ws = own-part← pw so ws
own-part← (d-fundef ∷ pw) (so-other ns-def so)    ws = own-part← pw so ws
own-part← (d-alias ∷ pw)    (so-other ns-alias so)  ws = own-part← pw so ws
own-part← (d-import ∷ pw)   (so-other ns-import so) ws = own-part← pw so ws

------------------------------------------------------------------------
-- The imports' signatures
------------------------------------------------------------------------

imp-module← : ∀ {p′ ds₂ ds₂′ Σ₁} → Pointwise DEmb ds₂ ds₂′ → SignaturesOf p′ ds₂′ Σ₁ → WellFormed Σ₁
            → Σ[ fs ∈ List Entry ] XAlign (Parser.importedSigs (sigsOf p′ ds₂)) fs × (toISig Σ₁ ≡ entrySig fs) × All FFIFacts fs
imp-module← [] so-nil [] = [] , xa-nil , refl , []
imp-module← {p′} (d-signature {x = x} {A = A} ∷ pw) (so-sig {t = t} dto so) (w ∷ ws) =
  let (fs , xa , ti , fa) = imp-module← pw so ws
  in _ , xa-sig (project-of n A dto w) xa , cong (_ ∷_) ti , ffi-facts t {n = n} {b = RVar n} dto w ∷ fa
  where n = showCanonical (canonical (p′ ++ x ∷ []))
imp-module← (d-typesig ∷ pw)  (so-other ns-tsig so)   ws = imp-module← pw so ws
imp-module← (d-fundef ∷ pw) (so-other ns-def so)    ws = imp-module← pw so ws
imp-module← (d-alias ∷ pw)    (so-other ns-alias so)  ws = imp-module← pw so ws
imp-module← (d-import ∷ pw)   (so-other ns-import so) ws = imp-module← pw so ws

-- The imports' signatures, read from the module map (`importedOf`).
imp-part← : ∀ {mm mm′ um am dsU dsR ds′ Σᵢ} → ModRel mm mm′ → LR.ResolvesDecls mm um am dsU dsR
          → Pointwise DEmb dsU ds′ → Imported mm′ ds′ Σᵢ → WellFormed Σᵢ
          → Σ[ fs ∈ List Entry ] XAlign (Parser.importedSigs (importedOf mm dsU)) fs × (toISig Σᵢ ≡ entrySig fs) × All FFIFacts fs
imp-part← mr LR.rds-nil [] im-nil [] = [] , xa-nil , refl , []
imp-part← mr (LR.rds-cons LR.nim-fundef (LR.rd-fundef _ _) rds) (d-fundef ∷ pw) (im-other ni-def im) ws = imp-part← mr rds pw im ws
imp-part← mr (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) (d-typesig ∷ pw) (im-other ni-tsig im) ws = imp-part← mr rds pw im ws
imp-part← mr (LR.rds-cons LR.nim-sig LR.rd-signature rds) (d-signature ∷ pw) (im-other ni-sig im) ws =
  imp-part← mr rds pw im ws
imp-part← mr (LR.rds-cons LR.nim-alias LR.rd-typealias rds) (d-alias ∷ pw) (im-other ni-alias im) ws = imp-part← mr rds pw im ws
imp-part← {mm = mm} {dsU = DImport (mkImport p a) ∷ dsU′} mr (LR.rds-import {impDs = impDs} fa rds) (d-import ∷ pw)
          (im-import {Σ₁ = Σ₁} {Σ₂ = Σ₂} fa₂ ex so₁ im₂) ws =
  let (ds₂″ , fa″ , pw₂) = find mr fa
      pw₂′ = subst (Pointwise DEmb impDs) (first-unique fa″ fa₂) pw₂
      so₁′ = subst (λ q → SignaturesOf q _ Σ₁) (expands-unique ex (expands-of p)) so₁
      (w₁ , w₂) = wf-++ Σ₁ ws
      X = sigsOf (expandPath p) impDs
      (fsX , xX , tX , fX) = imp-module← pw₂′ so₁′ w₁
      (fsR , xR , tR , fR) = imp-part← mr rds pw im₂ w₂
      xa = subst (λ l → XAlign l (fsX ++ fsR))
             (sym (trans (cong (λ m → Parser.importedSigs (importedAt (expandPath p) m ++ importedOf mm dsU′)) (lookupMod-complete mm p _ fa))
                         (importedSigs-++ X (importedOf mm dsU′))))
             (xa-++ xX xR)
  in fsX ++ fsR , xa
     , trans (toISig-++ Σ₁ Σ₂) (trans (cong₂ _++_ tX tR) (sym (sigs-table-++ (imported-sigs X) xX fsR)))
     , all-++ fX fR
