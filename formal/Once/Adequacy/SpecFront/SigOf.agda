-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SigOf — the program's signature, the Spec's from
-- the compiler's (plan 0.121 §3.6, F6).
--
-- The compiler's signature table is its FFI entries: the module's own
-- `signature`s, then its imports' read from the module map (`sigsFirst`,
-- `Resolved.imported`), each at the type the
-- extractor reads (`projectSig`), concrete and honest (the typed telescope's
-- facts, `FFIFacts`). The Spec's is `SignatureOf`: its own `signature`s
-- (`SignaturesOf []`), then its imports' (`Imported`), each a declaration
-- type of the written type. From the compiler's, the Spec's: its own part
-- (`own-part`) and its imports' (`imp-part`), whose table is the compiler's
-- (`toISig`): the same names (an imported one's key is its canonical name,
-- R12) at the same types (`SigTypes.decl-eq`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.SigOf where

open import Data.List using (List)
open import Data.String using (String)

open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.String.Properties as StrProp

import Once.Internal.Type as LT

import Once.Spec.Type as LT
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type.Honest using (HonestFFI)
open import Once.Internal.Contract using (ISig)
open import Once.Spec.Name using (canonical)
open import Once.Internal.Name using (showCanonical)
open import Once.Spec.Signature using (Signature; _∶_)
import Once.Spec.Surface.Syntax as S
open import Once.Spec.Surface.Program using (SignatureOf; SignaturesOf; so-nil; so-sig; so-other; ns-tsig; ns-def; ns-alias; ns-import;
  Imported; im-nil; im-import; im-other; ni-sig; ni-tsig; ni-def; ni-alias)
import Once.Spec.Surface.Resolution as SR
import Once.Parser as Parser
import Once.Adequacy.SpecGrammar.Conv
import Once.Spec.Surface.Program
open Parser.FunInfo using (funType)
open import Once.Spec.Surface.Syntax using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Spec.Surface.Syntax using (mkImport)
open import Once.Parser.Module.Resolve using (sigsOf; importedAt; importedOf; expandPath)
open import Once.Adequacy.ResolveBridge using (lookupMod-complete)
open import Once.Spec.Surface.Syntax using (PolyType)
import Once.Internal.Resolution as LR
open import Once.Internal.Module using (entrySig)
open import Once.Adequacy.SpecInterp using (declTy)
open import Once.Internal.Core.Decl using (toISig)
open import Once.Adequacy.SpecFront.Extract using (XAlign; xa-nil; xa-pass; xa-mono; xa-poly; xa-nosig; xa-sig; project-ok; IsSig; is-sig; sigs-split′; own-sigs; imported-sigs; FFIFacts; nonSigs-none; FFIEntry; ffi-of)
open import Once.Adequacy.SpecFront.SigTypes using (decl-of; decl-eq)
open import Once.Adequacy.SpecFront.Resolve using (first→)

private
  -- a signature's Spec reading, at the compiler's type
  read-sig : ∀ n T {ty} → Parser.projectSig n T ≡ inj₂ ty → IsConcrete ty → HonestFFI ty
           → Σ[ t ∈ _ ] Once.Spec.Surface.Program.DeclTypeOf (Once.Adequacy.SpecGrammar.Conv.toPoly T) t × declTy t ≡ ty
  read-sig n T ps c h =
    let (g , ig , e) = project-ok n T ps
        (t , dto) = decl-of T g (subst IsConcrete e c) (subst HonestFFI e h)
    in t , dto , trans (decl-eq T g dto) (sym e)

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

own-part : ∀ dsU {fs} → XAlign (Parser.ownSigs dsU) fs → All FFIFacts fs
         → Σ[ Σ₀ ∈ Signature ] SignaturesOf [] dsU Σ₀ × (toISig Σ₀ ≡ entrySig fs)
own-part [] xa-nil [] = [] , so-nil , refl
own-part (DSignature x A ∷ ds) (xa-sig ps xa) ((_ , ty , refl , c , h) ∷ fa) =
  let (t , dto , e) = read-sig x A ps c h ; (Σ₀ , so , ti) = own-part ds xa fa
  in _ , so-sig dto so , cong₂ _∷_ (cong (x ,_) e) ti
own-part (DTypeSig _ _ ∷ ds)     xa fa = let (Σ₀ , so , ti) = own-part ds xa fa in Σ₀ , so-other ns-tsig so , ti
own-part (DFunDef _ _ ∷ ds)      xa fa = let (Σ₀ , so , ti) = own-part ds xa fa in Σ₀ , so-other ns-def so , ti
own-part (DTypeAlias _ _ _ ∷ ds) xa fa = let (Σ₀ , so , ti) = own-part ds xa fa in Σ₀ , so-other ns-alias so , ti
own-part (DImport _ ∷ ds)        xa fa = let (Σ₀ , so , ti) = own-part ds xa fa in Σ₀ , so-other ns-import so , ti

------------------------------------------------------------------------
-- The imports' signatures
------------------------------------------------------------------------

-- An imported module's signatures, under its path (`sigsOf`).
imp-module : ∀ {p′} ds₂ {fs} → XAlign (Parser.importedSigs (sigsOf p′ ds₂)) fs → All FFIFacts fs
           → Σ[ Σ₁ ∈ Signature ] SignaturesOf p′ ds₂ Σ₁ × (toISig Σ₁ ≡ entrySig fs)
imp-module [] xa-nil [] = [] , so-nil , refl
imp-module {p′} (DSignature x A ∷ ds) (xa-sig ps xa) ((_ , ty , refl , c , h) ∷ fa) =
  let (t , dto , e) = read-sig (showCanonical (canonical (p′ ++ x ∷ []))) A ps c h ; (Σ₁ , so , ti) = imp-module ds xa fa
  in _ , so-sig dto so , cong₂ _∷_ (cong (_ ,_) e) ti
imp-module (DTypeSig _ _ ∷ ds)     xa fa = let (Σ₁ , so , ti) = imp-module ds xa fa in Σ₁ , so-other ns-tsig so , ti
imp-module (DFunDef _ _ ∷ ds)      xa fa = let (Σ₁ , so , ti) = imp-module ds xa fa in Σ₁ , so-other ns-def so , ti
imp-module (DTypeAlias _ _ _ ∷ ds) xa fa = let (Σ₁ , so , ti) = imp-module ds xa fa in Σ₁ , so-other ns-alias so , ti
imp-module (DImport _ ∷ ds)        xa fa = let (Σ₁ , so , ti) = imp-module ds xa fa in Σ₁ , so-other ns-import so , ti

importedSigs-++ : ∀ (xs ys : List (String × PolyType)) → Parser.importedSigs (xs ++ ys) ≡ Parser.importedSigs xs ++ Parser.importedSigs ys
importedSigs-++ []       ys = refl
importedSigs-++ (x ∷ xs) ys = cong (_ ∷_) (importedSigs-++ xs ys)

-- resolution keeps the module's own signatures
own-res : ∀ {mm um am dsU dsR} → LR.ResolvesDecls mm um am dsU dsR → Parser.ownSigs dsR ≡ Parser.ownSigs dsU
own-res LR.rds-nil = refl
own-res (LR.rds-cons LR.nim-fundef (LR.rd-fundef _ _) rds) = own-res rds
own-res (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) = own-res rds
own-res (LR.rds-cons LR.nim-sig LR.rd-signature rds) = cong (_ ∷_) (own-res rds)
own-res (LR.rds-cons LR.nim-alias LR.rd-typealias rds) = own-res rds
own-res (LR.rds-import _ rds) = own-res rds

expands-of : ∀ p → SR.Expands p (expandPath p)
expands-of [] = SR.ex-nil
expands-of (c ∷ rest) with c Data.String.≟ "I"
... | yes refl = SR.ex-I
... | no ne    = SR.ex-other ne

-- The imports' signatures, read from the module map (`importedOf`): the Spec's
-- `Imported`, whose table is the FFI entries'.
imp-part : ∀ {mm um am dsU dsR fs} → LR.ResolvesDecls mm um am dsU dsR
         → XAlign (Parser.importedSigs (importedOf mm dsU)) fs → All FFIFacts fs
         → Σ[ Σᵢ ∈ Signature ] Imported mm dsU Σᵢ × (toISig Σᵢ ≡ entrySig fs)
imp-part LR.rds-nil xa-nil [] = [] , im-nil , refl
imp-part (LR.rds-cons LR.nim-fundef (LR.rd-fundef _ _) rds) xa fa =
  let (Σᵢ , im , ti) = imp-part rds xa fa in Σᵢ , im-other ni-def im , ti
imp-part (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) xa fa =
  let (Σᵢ , im , ti) = imp-part rds xa fa in Σᵢ , im-other ni-tsig im , ti
imp-part (LR.rds-cons LR.nim-sig LR.rd-signature rds) xa fa =
  let (Σᵢ , im , ti) = imp-part rds xa fa in Σᵢ , im-other ni-sig im , ti
imp-part (LR.rds-cons LR.nim-alias LR.rd-typealias rds) xa fa =
  let (Σᵢ , im , ti) = imp-part rds xa fa in Σᵢ , im-other ni-alias im , ti
imp-part {mm = mm} {dsU = DImport (mkImport p a) ∷ dsU′} (LR.rds-import {impDs = impDs} fa rds) xa fs-ok =
  let X   = sigsOf (expandPath p) impDs
      xa′ = subst (λ l → XAlign l _)
              (trans (cong (λ m → Parser.importedSigs (importedAt (expandPath p) m ++ importedOf mm dsU′)) (lookupMod-complete mm p _ fa))
                     (importedSigs-++ X (importedOf mm dsU′))) xa
      (fsX , fs′ , e , xX , xr) = sigs-split′ (Parser.importedSigs X) (Parser.importedSigs (importedOf mm dsU′)) (imported-sigs X) xa′
      fa″ = subst (All FFIFacts) e fs-ok
      faX = AllP.++⁻ˡ fsX fa″
      faR = AllP.++⁻ʳ fsX fa″
      (Σ₁ , so₁ , ti₁) = imp-module impDs xX faX
      (Σ₂ , im₂ , ti₂) = imp-part rds xr faR
  in Σ₁ ++ Σ₂ , im-import (first→ fa) (expands-of p) so₁ im₂
     , trans (toISig-++ Σ₁ Σ₂) (trans (cong₂ _++_ ti₁ ti₂) (sym (trans (cong entrySig e) (entrySig-++ fsX fs′ faX))))

------------------------------------------------------------------------
-- The program's signature
------------------------------------------------------------------------

private
  -- the definitions' entries add nothing to the table
  defs-table : ∀ {ds es} → XAlign ds es → All (λ d → ¬ IsSig d) ds → entrySig es ≡ []
  defs-table xa-nil _ = refl
  defs-table (xa-pass _ xa) (_ ∷ n) = defs-table xa n
  defs-table (xa-mono _ xa) (_ ∷ _ ∷ n) = defs-table xa n
  defs-table (xa-poly _ xa) (_ ∷ _ ∷ n) = defs-table xa n
  defs-table (xa-nosig xa) (_ ∷ n) = defs-table xa n
  defs-table (xa-sig _ _) (n ∷ _) = ⊥-elim (n is-sig)

-- The extractor's signature prefix (own `signature`s, then the imports') is
-- the Spec's `SignatureOf`, whose table is the prefix's.
signature-of : ∀ {mm um am dsU dsR es} → LR.ResolvesDecls mm um am dsU dsR
             → XAlign (Parser.sigsFirst dsR (importedOf mm dsU)) es
             → Σ[ fs ∈ List Parser.Entry ] Σ[ es′ ∈ List Parser.Entry ] (es ≡ fs ++ es′) × XAlign (Parser.nonSigs dsR) es′ × All FFIEntry fs
               × (All FFIFacts fs → Σ[ Σₛ ∈ Signature ] SignatureOf mm dsU Σₛ × (toISig Σₛ ≡ entrySig fs) × (entrySig es ≡ entrySig fs))
signature-of {mm = mm} {dsU = dsU} {dsR = dsR} rds xa =
  let (f₁ , r₁ , e₁ , x₁ , xr) = sigs-split′ (Parser.ownSigs dsR) _ (own-sigs dsR) xa
      (f₂ , r₂ , e₂ , x₂ , xn) = sigs-split′ (Parser.importedSigs (importedOf mm dsU)) _ (imported-sigs (importedOf mm dsU)) xr
      ees = trans e₁ (trans (cong (f₁ ++_) e₂) (sym (++-assoc f₁ f₂ r₂)))
  in f₁ ++ f₂ , r₂ , ees , xn , AllP.++⁺ (ffi-of (own-sigs dsR) x₁) (ffi-of (imported-sigs (importedOf mm dsU)) x₂) ,
     λ fa → let fa₁ = AllP.++⁻ˡ f₁ fa ; fa₂ = AllP.++⁻ʳ f₁ fa
                (Σ₀ , so , t₀) = own-part dsU (subst (λ l → XAlign l f₁) (own-res rds) x₁) fa₁
                (Σᵢ , im , tᵢ) = imp-part rds x₂ fa₂
            in Σ₀ ++ Σᵢ , (Σ₀ , Σᵢ , so , im , refl)
               , trans (toISig-++ Σ₀ Σᵢ) (trans (cong₂ _++_ t₀ tᵢ) (sym (entrySig-++ f₁ f₂ fa₁)))
               , trans (cong entrySig ees) (trans (entrySig-++ (f₁ ++ f₂) r₂ fa)
                   (trans (cong (entrySig (f₁ ++ f₂) ++_) (defs-table xn (nonSigs-none dsR))) (++-identityʳ _)))
