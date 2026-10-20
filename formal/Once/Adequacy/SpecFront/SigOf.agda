-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SigOf — the program's signature, the Spec's from
-- the compiler's (plan 0.121 §3.6, F6).
--
-- The compiler's signature table is its FFI entries: the module's own
-- `signature`s, then its imports' (`sigsFirst`), each at the type the
-- extractor reads (`projectSig`), concrete and honest (the typed telescope's
-- facts, `FFIFacts`). The Spec's is `SignatureOf`: its own `signature`s
-- (`SignaturesOf []`), then its imports' (`Imported`), each a declaration
-- type of the written type. From the compiler's, the Spec's: its own part
-- (`own-part`) and its imports' (`imp-part`), whose table is the compiler's
-- (`toISig`): the same names (an imported one's key is its canonical name,
-- R12) at the same types (`SigTypes.decl-eq`).
------------------------------------------------------------------------

open import Data.List using (List)
open import Data.String using (String)

module Once.Adequacy.SpecFront.SigOf (ps : List String) where

open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Bool using (true; false)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.String.Properties as StrProp

import Once.Lang.Type as LT
open import Once.Lang.Type.WellFormed using (IsConcrete)
open import Once.Lang.Type.Honest using (HonestFFI)
open import Once.Lang.Contract using (ISig)
open import Once.Spec.Name using (canonical)
open import Once.Lang.Name using (showCanonical)
open import Once.Spec.Signature using (Signature; _∶_)
import Once.Spec.Surface.Syntax as S
open import Once.Spec.Surface.Program using (SignatureOf; SignaturesOf; so-nil; so-sig; so-other; ns-tsig; ns-def; ns-alias; ns-import;
  Imported; im-nil; im-import; im-other; ni-sig; ni-tsig; ni-def; ni-alias)
import Once.Spec.Surface.Resolution as SR
import Once.Parser as Parser
import Once.Adequacy.SpecGrammar.Conv
import Once.Spec.Surface.Program
open Parser.FunInfo using (funType)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; mkImport)
open import Once.Parser.Module.Resolve using (signaturesWithOwner; expandPath)
import Once.Lang.Resolution as LR
open import Once.Lang.Module using (entrySig)
open import Once.Adequacy.SpecInterp using (toISig; declTy)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-fundef; d-signature; d-alias; d-import)
open import Once.Adequacy.SpecFront.Extract using (XAlign; xa-nil; xa-sig; xa-isig; project-ok; IsSig; is-sig; sigs-split′; own-sigs; imported-sigs)
open import Once.Adequacy.SpecFront.SigTypes using (decl-of; decl-eq)
open import Once.Adequacy.SpecFront.Align Data.List.[] ps using (expand-id)
open import Once.Adequacy.SpecFront.ModRel using (ModRel; find)

-- An FFI entry's facts (the typed telescope's).
FFIFacts : Parser.Entry → Set
FFIFacts (Parser.e-fun fi)  = (Parser.FunInfo.funIsPrimitive fi ≡ true) × Σ[ ty ∈ LT.Type ] (funType fi ≡ just ty) × IsConcrete ty × HonestFFI ty
FFIFacts (Parser.e-poly _)  = ⊥

private
  -- a signature's Spec reading, at the compiler's type
  read-sig : ∀ al n T {ty} → Parser.projectSig al n T ≡ inj₂ ty → IsConcrete ty → HonestFFI ty
           → Σ[ t ∈ _ ] Once.Spec.Surface.Program.DeclTypeOf (Once.Adequacy.SpecGrammar.Conv.toPoly T) t × declTy t ≡ ty
  read-sig al n T ps c h =
    let (g , ig , e) = project-ok al n T ps
        e′ = trans e (expand-id al _)
        (t , dto) = decl-of T g (subst IsConcrete e′ c) (subst HonestFFI e′ h)
    in t , dto , trans (decl-eq T g dto) (sym e′)

  toISig-++ : ∀ (Σ₁ Σ₂ : Signature) → toISig (Σ₁ ++ Σ₂) ≡ toISig Σ₁ ++ toISig Σ₂
  toISig-++ []        Σ₂ = refl
  toISig-++ (d ∷ Σ₁) Σ₂ = cong (_ ∷_) (toISig-++ Σ₁ Σ₂)

  -- the FFI entries' table distributes
  entrySig-++ : ∀ (fs es : List Parser.Entry) → All FFIFacts fs → entrySig (fs ++ es) ≡ entrySig fs ++ entrySig es
  entrySig-++ [] es [] = refl
  entrySig-++ (Parser.e-fun (Parser.mkFunInfo n (just ty) b true) ∷ fs) es ((refl , _ , refl , _ , _) ∷ fa) = cong (_ ∷_) (entrySig-++ fs es fa)

------------------------------------------------------------------------
-- The module's own signatures
------------------------------------------------------------------------

own-part : ∀ {al dsU ds′ fs} → Pointwise DEmb dsU ds′ → XAlign al (Parser.ownSigs dsU) fs → All FFIFacts fs
         → Σ[ Σ₀ ∈ Signature ] SignaturesOf [] ds′ Σ₀ × (toISig Σ₀ ≡ entrySig fs)
own-part [] xa-nil [] = [] , so-nil , refl
own-part {al} (d-signature {x = x} {A = A} ∷ pw) (xa-sig ps xa) ((_ , ty , refl , c , h) ∷ fa) =
  let (t , dto , e) = read-sig al x A ps c h ; (Σ₀ , so , ti) = own-part pw xa fa
  in _ , so-sig dto so , cong₂ _∷_ (cong (x ,_) e) ti
own-part (d-typesig ∷ pw)  xa fa = let (Σ₀ , so , ti) = own-part pw xa fa in Σ₀ , so-other ns-tsig so , ti
own-part (d-fundef _ ∷ pw) xa fa = let (Σ₀ , so , ti) = own-part pw xa fa in Σ₀ , so-other ns-def so , ti
own-part (d-alias ∷ pw)    xa fa = let (Σ₀ , so , ti) = own-part pw xa fa in Σ₀ , so-other ns-alias so , ti
own-part (d-import ∷ pw)   xa fa = let (Σ₀ , so , ti) = own-part pw xa fa in Σ₀ , so-other ns-import so , ti

------------------------------------------------------------------------
-- The imports' signatures
------------------------------------------------------------------------

-- An imported module's signatures, owned by its path.
imp-module : ∀ {al p′ ds₂ ds₂′ fs} → Pointwise DEmb ds₂ ds₂′ → XAlign al (signaturesWithOwner (just p′) ds₂) fs → All FFIFacts fs
           → Σ[ Σ₁ ∈ Signature ] SignaturesOf p′ ds₂′ Σ₁ × (toISig Σ₁ ≡ entrySig fs)
imp-module [] xa-nil [] = [] , so-nil , refl
imp-module {al} {p′} (d-signature {x = x} {A = A} ∷ pw) (xa-isig ps xa) ((_ , ty , refl , c , h) ∷ fa) =
  let (t , dto , e) = read-sig al (showCanonical (canonical (p′ ++ x ∷ []))) A ps c h ; (Σ₁ , so , ti) = imp-module pw xa fa
  in _ , so-sig dto so , cong₂ _∷_ (cong (_ ,_) e) ti
imp-module (d-typesig ∷ pw)  xa fa = let (Σ₁ , so , ti) = imp-module pw xa fa in Σ₁ , so-other ns-tsig so , ti
imp-module (d-fundef _ ∷ pw) xa fa = let (Σ₁ , so , ti) = imp-module pw xa fa in Σ₁ , so-other ns-def so , ti
imp-module (d-alias ∷ pw)    xa fa = let (Σ₁ , so , ti) = imp-module pw xa fa in Σ₁ , so-other ns-alias so , ti
imp-module (d-import ∷ pw)   xa fa = let (Σ₁ , so , ti) = imp-module pw xa fa in Σ₁ , so-other ns-import so , ti

private
  owned-sigs : ∀ (o : List String) ds → All IsSig (signaturesWithOwner (just o) ds)
  owned-sigs o [] = []
  owned-sigs o (DSignature _ _ _ ∷ ds) = is-sig ∷ owned-sigs o ds
  owned-sigs o (DTypeSig _ _ ∷ ds) = owned-sigs o ds
  owned-sigs o (DFunDef _ _ ∷ ds) = owned-sigs o ds
  owned-sigs o (DTypeAlias _ _ _ ∷ ds) = owned-sigs o ds
  owned-sigs o (DImport _ ∷ ds) = owned-sigs o ds

  imported-owned : ∀ (o : List String) ds rest
                 → Parser.importedSigs (signaturesWithOwner (just o) ds ++ rest) ≡ signaturesWithOwner (just o) ds ++ Parser.importedSigs rest
  imported-owned o [] rest = refl
  imported-owned o (DSignature _ _ _ ∷ ds) rest = cong (_ ∷_) (imported-owned o ds rest)
  imported-owned o (DTypeSig _ _ ∷ ds) rest = imported-owned o ds rest
  imported-owned o (DFunDef _ _ ∷ ds) rest = imported-owned o ds rest
  imported-owned o (DTypeAlias _ _ _ ∷ ds) rest = imported-owned o ds rest
  imported-owned o (DImport _ ∷ ds) rest = imported-owned o ds rest

  own-owned : ∀ (o : List String) ds rest
            → Parser.ownSigs (signaturesWithOwner (just o) ds ++ rest) ≡ Parser.ownSigs rest
  own-owned o [] rest = refl
  own-owned o (DSignature _ _ _ ∷ ds) rest = own-owned o ds rest
  own-owned o (DTypeSig _ _ ∷ ds) rest = own-owned o ds rest
  own-owned o (DFunDef _ _ ∷ ds) rest = own-owned o ds rest
  own-owned o (DTypeAlias _ _ _ ∷ ds) rest = own-owned o ds rest
  own-owned o (DImport _ ∷ ds) rest = own-owned o ds rest

  -- resolution keeps the module's own signatures
  own-res : ∀ {mm um am dsU dsR} → LR.ResolvesDecls mm ps um am dsU dsR → Parser.ownSigs dsR ≡ Parser.ownSigs dsU
  own-res LR.rds-nil = refl
  own-res (LR.rds-cons LR.nim-fundef (LR.rd-fundef _ _) rds) = own-res rds
  own-res (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) = own-res rds
  own-res (LR.rds-cons LR.nim-sig (LR.rd-signature {o = nothing}) rds) = cong (_ ∷_) (own-res rds)
  own-res (LR.rds-cons LR.nim-sig (LR.rd-signature {o = just _}) rds) = own-res rds
  own-res (LR.rds-cons LR.nim-alias LR.rd-typealias rds) = own-res rds
  own-res (LR.rds-import {imp = mkImport p (just _)} {impDs = impDs} {ds' = dsR′} _ rds) = trans (own-owned (expandPath p) impDs dsR′) (own-res rds)
  own-res (LR.rds-import {imp = mkImport p nothing} {impDs = impDs} {ds' = dsR′} _ rds) = trans (own-owned (expandPath p) impDs dsR′) (own-res rds)

  expands-of : ∀ p → SR.Expands p (expandPath p)
  expands-of [] = SR.ex-nil
  expands-of (c ∷ rest) with c Data.String.≟ "I"
  ... | yes refl = SR.ex-I
  ... | no ne    = SR.ex-other ne


imp-part : ∀ {al mm mm′ um am dsU dsR ds′ fs} → ModRel mm mm′ → LR.ResolvesDecls mm ps um am dsU dsR → Pointwise DEmb dsU ds′
         → XAlign al (Parser.importedSigs dsR) fs → All FFIFacts fs
         → Σ[ Σᵢ ∈ Signature ] Imported mm′ ds′ Σᵢ × (toISig Σᵢ ≡ entrySig fs)
imp-part mr LR.rds-nil [] xa-nil [] = [] , im-nil , refl
imp-part mr (LR.rds-cons LR.nim-fundef (LR.rd-fundef _ _) rds) (d-fundef _ ∷ pw) xa fa =
  let (Σᵢ , im , ti) = imp-part mr rds pw xa fa in Σᵢ , im-other ni-def im , ti
imp-part mr (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) (d-typesig ∷ pw) xa fa =
  let (Σᵢ , im , ti) = imp-part mr rds pw xa fa in Σᵢ , im-other ni-tsig im , ti
imp-part mr (LR.rds-cons LR.nim-sig LR.rd-signature rds) (d-signature ∷ pw) xa fa =
  let (Σᵢ , im , ti) = imp-part mr rds pw xa fa in Σᵢ , im-other ni-sig im , ti
imp-part mr (LR.rds-cons LR.nim-alias LR.rd-typealias rds) (d-alias ∷ pw) xa fa =
  let (Σᵢ , im , ti) = imp-part mr rds pw xa fa in Σᵢ , im-other ni-alias im , ti
imp-part {al} mr (LR.rds-import {imp = mkImport p a} {impDs = impDs} {ds' = dsR′} fa rds) (d-import ∷ pw) xa fs-ok =
  imp-at a xa fs-ok
  where
    X = signaturesWithOwner (just (expandPath p)) impDs
    body : ∀ (a′ : Maybe String) {fs} → XAlign al (X ++ Parser.importedSigs dsR′) fs → All FFIFacts fs
         → Σ[ Σᵢ ∈ Signature ] Imported _ (S.DImport (S.mkImport p a′) ∷ _) Σᵢ × (toISig Σᵢ ≡ entrySig fs)
    body a′ {fs} xa′ fa′ =
      let (fsX , fs′ , e , xX , xr) = sigs-split′ X (Parser.importedSigs dsR′) (owned-sigs (expandPath p) impDs) xa′
          fa″ = subst (All FFIFacts) e fa′
          faX = AllP.++⁻ˡ fsX fa″
          faR = AllP.++⁻ʳ fsX fa″
          (ds₂′ , fa₂ , pw₂) = find mr fa
          (Σ₁ , so₁ , ti₁) = imp-module pw₂ xX faX
          (Σ₂ , im₂ , ti₂) = imp-part mr rds pw xr faR
      in Σ₁ ++ Σ₂ , im-import fa₂ (expands-of p) so₁ im₂
         , trans (toISig-++ Σ₁ Σ₂) (trans (cong₂ _++_ ti₁ ti₂) (sym (trans (cong entrySig e) (entrySig-++ fsX fs′ faX))))
    imp-at : ∀ (a′ : Maybe String) {fs}
           → XAlign al (Parser.importedSigs (DImport (mkImport p a′) ∷ signaturesWithOwner (Once.Parser.Module.Resolve.ownerOf (mkImport p a′)) impDs ++ dsR′)) fs
           → All FFIFacts fs
           → Σ[ Σᵢ ∈ Signature ] Imported _ (S.DImport (S.mkImport p a′) ∷ _) Σᵢ × (toISig Σᵢ ≡ entrySig fs)
    imp-at (just x) xa′ fa′ = body (just x) (subst (λ l → XAlign al l _) (imported-owned (expandPath p) impDs dsR′) xa′) fa′
    imp-at nothing  xa′ fa′ = body nothing (subst (λ l → XAlign al l _) (imported-owned (expandPath p) impDs dsR′) xa′) fa′

------------------------------------------------------------------------
-- The program's signature
------------------------------------------------------------------------

-- The extractor's signature prefix (own `signature`s, then the imports') is
-- the Spec's `SignatureOf`, whose table is the prefix's.
signature-of : ∀ {al mm mm′ um am dsU dsR ds′ es} → ModRel mm mm′ → LR.ResolvesDecls mm ps um am dsU dsR → Pointwise DEmb dsU ds′
             → XAlign al (Parser.sigsFirst dsR) es
             → Σ[ fs ∈ List Parser.Entry ] Σ[ es′ ∈ List Parser.Entry ] (es ≡ fs ++ es′) × XAlign al (Parser.nonSigs dsR) es′
               × (All FFIFacts fs → Σ[ Σₛ ∈ Signature ] SignatureOf mm′ ds′ Σₛ × (toISig Σₛ ≡ entrySig fs))
signature-of {al} {dsR = dsR} mr rds pw xa =
  let (f₁ , r₁ , e₁ , x₁ , xr) = sigs-split′ (Parser.ownSigs dsR) _ (own-sigs dsR) xa
      (f₂ , r₂ , e₂ , x₂ , xn) = sigs-split′ (Parser.importedSigs dsR) _ (imported-sigs dsR) xr
  in f₁ ++ f₂ , r₂ , trans e₁ (trans (cong (f₁ ++_) e₂) (sym (++-assoc f₁ f₂ r₂))) , xn ,
     λ fa → let fa₁ = AllP.++⁻ˡ f₁ fa ; fa₂ = AllP.++⁻ʳ f₁ fa
                (Σ₀ , so , t₀) = own-part pw (subst (λ l → XAlign al l f₁) (own-res rds) x₁) fa₁
                (Σᵢ , im , tᵢ) = imp-part mr rds pw x₂ fa₂
            in Σ₀ ++ Σᵢ , (Σ₀ , Σᵢ , so , im , refl)
               , trans (toISig-++ Σ₀ Σᵢ) (trans (cong₂ _++_ t₀ tᵢ) (sym (entrySig-++ f₁ f₂ fa₁)))
