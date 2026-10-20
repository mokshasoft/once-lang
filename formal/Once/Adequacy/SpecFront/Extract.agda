-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Extract — the entries the compiler extracts from a
-- module's declarations (plan 0.121 §3.6, F6).
--
-- The compiler reads a resolved module's declarations into its telescope's
-- entries (`Parser.extractFunctions-go`, a fold with a pending signature).
-- `XAlign` says what it produced, declaration by declaration: a type
-- signature followed by its definition is a monomorphic entry when the type
-- is ground and concrete, a telescope entry otherwise; a definition alone a
-- monomorphic one without a type; a `signature` declaration an FFI entry; a
-- type alias or an import nothing (`extract-align`).
--
-- (The extractor is written with `with`; the proof follows it.)
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Extract where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _≟_; _++_)
open import Data.Unit using (⊤)
open import Data.Bool using (true; false)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∋_)

import Once.Lang.Type as LT
open import Once.Lang.Type.Poly using (PolyType; Ground; extractGround)
open import Once.Lang.Type.WellFormed using (IsConcrete)
open import Once.Type using (isGround)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Lang.Syntax using (RawExpr; RVar)
open import Once.Parser.Module.Core using (Decl; DTypeAlias; DTypeSig; DFunDef; DSignature; DImport)
open import Once.Parser.TypeAlias using (TypeAliasEnv; expandAliases)
open import Once.Parser
  using (Entry; e-fun; e-poly; mkFunInfo; mkPolyFunInfo; extractFunctions-go; extractFunctions-consFun; extractFunctions-consPoly;
         projectSig)

-- A declaration the extractor passes over.
data Passed : Decl → Set where
  pa-alias  : ∀ {n ps t} → Passed (DTypeAlias n ps t)
  pa-import : ∀ {i}      → Passed (DImport i)

-- A type signature's reading: ground and concrete (a monomorphic entry at it),
-- or not (a telescope entry at the signature as written).
data SigReading (al : TypeAliasEnv) (T : PolyType) : Maybe LT.Type → Set where
  sr-mono : ∀ (g : Ground T) (c : IsConcrete (extractGround T g)) → isGround T ≡ inj₁ g → isConcrete? (extractGround T g) ≡ just c
          → SigReading al T (just (expandAliases al (extractGround T g)))
  sr-open : ∀ {u} → isGround T ≡ inj₂ u → SigReading al T nothing
  sr-nonc : ∀ (g : Ground T) → isGround T ≡ inj₁ g → isConcrete? (extractGround T g) ≡ nothing → SigReading al T nothing

data XAlign (al : TypeAliasEnv) : List Decl → List Entry → Set where
  xa-nil   : XAlign al [] []
  xa-pass  : ∀ {d ds es} → Passed d → XAlign al ds es → XAlign al (d ∷ ds) es
  xa-mono  : ∀ {x T b ty ds es} → SigReading al T (just ty) → XAlign al ds es
           → XAlign al (DTypeSig x T ∷ DFunDef x b ∷ ds) (e-fun (mkFunInfo x (just ty) b false) ∷ es)
  xa-poly  : ∀ {x T b ds es} → SigReading al T nothing → XAlign al ds es
           → XAlign al (DTypeSig x T ∷ DFunDef x b ∷ ds) (e-poly (mkPolyFunInfo x T b) ∷ es)
  xa-nosig : ∀ {x b ds es} → XAlign al ds es
           → XAlign al (DFunDef x b ∷ ds) (e-fun (mkFunInfo x nothing b false) ∷ es)
  xa-sig   : ∀ {x T ty ds es} → projectSig al x T ≡ inj₂ ty → XAlign al ds es
           → XAlign al (DSignature x nothing T ∷ ds) (e-fun (mkFunInfo x (just ty) (RVar x) true) ∷ es)
  xa-isig  : ∀ {x o T ty ds es} → projectSig al (o ++ "." ++ x) T ≡ inj₂ ty → XAlign al ds es
           → XAlign al (DSignature x (just o) T ∷ ds) (e-fun (mkFunInfo (o ++ "." ++ x) (just ty) (RVar (o ++ "." ++ x)) true) ∷ es)

private
  consFun-inj : ∀ (r : String ⊎ List Entry) fi {es} → extractFunctions-consFun r fi ≡ inj₂ es
              → Σ[ es′ ∈ List Entry ] (r ≡ inj₂ es′) × (es ≡ e-fun fi ∷ es′)
  consFun-inj (inj₁ _)   fi ()
  consFun-inj (inj₂ es′) fi refl = es′ , refl , refl

  consPoly-inj : ∀ (r : String ⊎ List Entry) n t b {es} → extractFunctions-consPoly r n t b ≡ inj₂ es
               → Σ[ es′ ∈ List Entry ] (r ≡ inj₂ es′) × (es ≡ e-poly (mkPolyFunInfo n t b) ∷ es′)
  consPoly-inj (inj₁ _)   n t b ()
  consPoly-inj (inj₂ es′) n t b refl = es′ , refl , refl

  fun-step : ∀ {al x ty b ds es} → extractFunctions-consFun (extractFunctions-go al ds nothing) (mkFunInfo x ty b false) ≡ inj₂ es
           → (∀ {es′} → extractFunctions-go al ds nothing ≡ inj₂ es′ → XAlign al ds es′)
           → Σ[ es′ ∈ List Entry ] (es ≡ e-fun (mkFunInfo x ty b false) ∷ es′) × XAlign al ds es′
  fun-step {al} {x} {ty} {b} {ds} eq rec =
    let (es′ , r , e) = consFun-inj (extractFunctions-go al ds nothing) (mkFunInfo x ty b false) eq in es′ , e , rec r

mutual
  extract-align : ∀ al ds {es} → extractFunctions-go al ds nothing ≡ inj₂ es → XAlign al ds es
  extract-align al [] refl = xa-nil
  extract-align al (DTypeSig name ty ∷ rest) eq with isGround ty in ig
  ... | inj₂ u = pending-poly al name ty rest (sr-open ig) eq
  ... | inj₁ g with isConcrete? (extractGround ty g) in ic
  ...   | just c  = pending-mono al name ty rest (sr-mono g c ig ic) eq
  ...   | nothing = pending-poly al name ty rest (sr-nonc g ig ic) eq
  extract-align al (DFunDef name body ∷ rest) eq =
    let (es′ , e , xa) = fun-step {al} {name} {nothing} {body} {rest} eq (extract-align al rest) in subst-es e (xa-nosig xa)
  extract-align al (DSignature name nothing ty ∷ rest) eq with projectSig al name ty in ps
  ... | inj₁ err = case-err eq
  ... | inj₂ gty =
    let (es′ , r , e) = consFun-inj (extractFunctions-go al rest nothing) (mkFunInfo name (just gty) (RVar name) true) eq
    in subst-es e (xa-sig ps (extract-align al rest r))
  extract-align al (DSignature name (just owner) ty ∷ rest) eq with projectSig al (owner ++ "." ++ name) ty in ps
  ... | inj₁ err = case-err eq
  ... | inj₂ gty =
    let (es′ , r , e) = consFun-inj (extractFunctions-go al rest nothing) (mkFunInfo (owner ++ "." ++ name) (just gty) (RVar (owner ++ "." ++ name)) true) eq
    in subst-es e (xa-isig ps (extract-align al rest r))
  extract-align al (DTypeAlias n ps t ∷ rest) eq = xa-pass pa-alias (extract-align al rest eq)
  extract-align al (DImport i ∷ rest) eq = xa-pass pa-import (extract-align al rest eq)

  -- a pending ground, concrete signature: its definition next
  pending-mono : ∀ al name T rest {ty es} → SigReading al T (just ty)
               → extractFunctions-go al rest (just (name , inj₁ ty)) ≡ inj₂ es → XAlign al (DTypeSig name T ∷ rest) es
  pending-mono al name T [] sr ()
  pending-mono al name T (DTypeSig _ _ ∷ rest) sr ()
  pending-mono al name T (DFunDef name′ body ∷ rest) {ty} sr eq with name ≟ name′
  ... | yes refl =
    let (es′ , e , xa) = fun-step {al} {name} {just ty} {body} {rest} eq (extract-align al rest) in subst-es e (xa-mono sr xa)
  ... | no _ = case-err eq
  pending-mono al name T (DSignature _ _ _ ∷ rest) sr ()
  pending-mono al name T (DTypeAlias _ _ _ ∷ rest) sr ()
  pending-mono al name T (DImport _ ∷ rest) sr ()

  -- a pending polymorphic (or non-concrete) signature: its definition next
  pending-poly : ∀ al name T rest {es} → SigReading al T nothing
               → extractFunctions-go al rest (just (name , inj₂ T)) ≡ inj₂ es → XAlign al (DTypeSig name T ∷ rest) es
  pending-poly al name T [] sr ()
  pending-poly al name T (DTypeSig _ _ ∷ rest) sr ()
  pending-poly al name T (DFunDef name′ body ∷ rest) sr eq with name ≟ name′
  ... | yes refl =
    let (es′ , r , e) = consPoly-inj (extractFunctions-go al rest nothing) name T body eq
    in subst-es e (xa-poly sr (extract-align al rest r))
  ... | no _ = case-err eq
  pending-poly al name T (DSignature _ _ _ ∷ rest) sr ()
  pending-poly al name T (DTypeAlias _ _ _ ∷ rest) sr ()
  pending-poly al name T (DImport _ ∷ rest) sr ()

  subst-es : ∀ {al ds es es′} → es ≡ es′ → XAlign al ds es′ → XAlign al ds es
  subst-es refl xa = xa

  case-err : ∀ {A : Set} {e : String} {es : List Entry} → (String ⊎ List Entry ∋ inj₁ e) ≡ inj₂ es → A
  case-err ()
