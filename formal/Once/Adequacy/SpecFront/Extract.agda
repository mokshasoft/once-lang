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

open import Data.List using (List; []; _∷_; _++_)
import Data.List
import Data.List.Properties
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties
import Relation.Binary.PropositionalEquality
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _≟_) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤)
open import Data.Bool using (true; false)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∋_)

import Once.Lang.Type as LT
open import Once.Lang.Type.Poly using (PolyType; Ground; extractGround)
open import Once.Lang.Type.WellFormed using (IsConcrete; RigidFree)
open import Once.Lang.Type.Honest using (HonestFFI)
open import Once.Type using (isGround)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Lang.Syntax using (RawExpr; RVar)
open import Once.Spec.Name using (canonical)
open import Once.Lang.Name using (showCanonical)
open import Once.Parser.Module.Core using (Decl; DTypeAlias; DTypeSig; DFunDef; DSignature; DImport)
open import Once.Parser.TypeAlias using (TypeAliasEnv; expandAliases)
open import Once.Parser
  using (Entry; e-fun; e-poly; mkFunInfo; mkPolyFunInfo; extractFunctions-go; extractFunctions-consFun; extractFunctions-consPoly;
         projectSig; honestSig)

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
  xa-isig  : ∀ {x o T ty ds es} → projectSig al (showCanonical (canonical (o ++ x ∷ []))) T ≡ inj₂ ty → XAlign al ds es
           → XAlign al (DSignature x (just o) T ∷ ds)
                    (e-fun (mkFunInfo (showCanonical (canonical (o ++ x ∷ []))) (just ty) (RVar (showCanonical (canonical (o ++ x ∷ [])))) true) ∷ es)

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
  extract-align al (DSignature name (just owner) ty ∷ rest) eq with projectSig al (showCanonical (canonical (owner ++ name ∷ []))) ty in ps
  ... | inj₁ err = case-err eq
  ... | inj₂ gty =
    let (es′ , r , e) = consFun-inj (extractFunctions-go al rest nothing) (mkFunInfo (showCanonical (canonical (owner ++ name ∷ []))) (just gty) (RVar (showCanonical (canonical (owner ++ name ∷ [])))) true) eq
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

------------------------------------------------------------------------
-- The signatures first (`sigsFirst`): their entries, then the definitions'
------------------------------------------------------------------------

data IsSig : Decl → Set where
  is-sig : ∀ {x o T} → IsSig (DSignature x o T)

-- An FFI entry.
FFIEntry : Entry → Set
FFIEntry (e-fun fi)  = Once.Parser.FunInfo.funIsPrimitive fi ≡ true
FFIEntry (e-poly _)  = ⊥

-- the signatures' entries are FFI entries
ffi-of : ∀ {al sigs fs} → All IsSig sigs → XAlign al sigs fs → All FFIEntry fs
ffi-of [] xa-nil = []
ffi-of (is-sig ∷ a) (xa-pass () xa)
ffi-of (is-sig ∷ a) (xa-sig _ xa) = refl ∷ ffi-of a xa
ffi-of (is-sig ∷ a) (xa-isig _ xa) = refl ∷ ffi-of a xa

-- An FFI entry's facts (the typed telescope's).
FFIFacts : Entry → Set
FFIFacts (e-fun fi)  = (Once.Parser.FunInfo.funIsPrimitive fi ≡ true) × Σ[ ty ∈ LT.Type ] (Once.Parser.FunInfo.funType fi ≡ just ty) × IsConcrete ty × HonestFFI ty × RigidFree ty
FFIFacts (e-poly _)  = ⊥

own-sigs : ∀ ds → All IsSig (Once.Parser.ownSigs ds)
own-sigs [] = []
own-sigs (DSignature n nothing t ∷ ds) = is-sig ∷ own-sigs ds
own-sigs (DSignature n (just o) t ∷ ds) = own-sigs ds
own-sigs (DTypeSig _ _ ∷ ds) = own-sigs ds
own-sigs (DFunDef _ _ ∷ ds) = own-sigs ds
own-sigs (DTypeAlias _ _ _ ∷ ds) = own-sigs ds
own-sigs (DImport _ ∷ ds) = own-sigs ds

-- (and the rest none)
nonSigs-none : ∀ ds → All (λ d → ¬ IsSig d) (Once.Parser.nonSigs ds)
nonSigs-none [] = []
nonSigs-none (DSignature _ _ _ ∷ ds) = nonSigs-none ds
nonSigs-none (DTypeSig _ _ ∷ ds) = (λ ()) ∷ nonSigs-none ds
nonSigs-none (DFunDef _ _ ∷ ds) = (λ ()) ∷ nonSigs-none ds
nonSigs-none (DTypeAlias _ _ _ ∷ ds) = (λ ()) ∷ nonSigs-none ds
nonSigs-none (DImport _ ∷ ds) = (λ ()) ∷ nonSigs-none ds

imported-sigs : ∀ ds → All IsSig (Once.Parser.importedSigs ds)
imported-sigs [] = []
imported-sigs (DSignature n nothing t ∷ ds) = imported-sigs ds
imported-sigs (DSignature n (just o) t ∷ ds) = is-sig ∷ imported-sigs ds
imported-sigs (DTypeSig _ _ ∷ ds) = imported-sigs ds
imported-sigs (DFunDef _ _ ∷ ds) = imported-sigs ds
imported-sigs (DTypeAlias _ _ _ ∷ ds) = imported-sigs ds
imported-sigs (DImport _ ∷ ds) = imported-sigs ds

-- Signatures before the rest: their FFI entries before the rest's.
sigs-split : ∀ {al} (sigs rest : List Decl) {es} → All IsSig sigs → XAlign al (sigs ++ rest) es
           → Σ[ fs ∈ List Entry ] Σ[ es′ ∈ List Entry ] (es ≡ fs Data.List.++ es′) × All FFIEntry fs × XAlign al rest es′
sigs-split [] rest [] xa = [] , _ , refl , [] , xa
sigs-split (DSignature x nothing T ∷ sigs) rest (is-sig ∷ as) (xa-sig ps xa) =
  let (fs , es′ , e , ffs , xa′) = sigs-split sigs rest as xa in _ ∷ fs , es′ , Relation.Binary.PropositionalEquality.cong (_ ∷_) e , refl ∷ ffs , xa′
sigs-split (DSignature x (just o) T ∷ sigs) rest (is-sig ∷ as) (xa-isig ps xa) =
  let (fs , es′ , e , ffs , xa′) = sigs-split sigs rest as xa in _ ∷ fs , es′ , Relation.Binary.PropositionalEquality.cong (_ ∷_) e , refl ∷ ffs , xa′

-- The extractor's entries: the signatures' FFI entries, then the definitions'.
sigsFirst-split : ∀ {al} ds {es} → XAlign al (Once.Parser.sigsFirst ds) es
                → Σ[ fs ∈ List Entry ] Σ[ es′ ∈ List Entry ] (es ≡ fs Data.List.++ es′) × All FFIEntry fs × XAlign al (Once.Parser.nonSigs ds) es′
sigsFirst-split {al} ds xa =
  let (fs₁ , r₁ , e₁ , f₁ , xa₁) = sigs-split (Once.Parser.ownSigs ds) _ (own-sigs ds) xa
      (fs₂ , r₂ , e₂ , f₂ , xa₂) = sigs-split (Once.Parser.importedSigs ds) _ (imported-sigs ds) xa₁
  in fs₁ Data.List.++ fs₂ , r₂
     , Relation.Binary.PropositionalEquality.trans e₁
         (Relation.Binary.PropositionalEquality.trans (Relation.Binary.PropositionalEquality.cong (fs₁ Data.List.++_) e₂)
           (Relation.Binary.PropositionalEquality.sym (Data.List.Properties.++-assoc fs₁ fs₂ r₂)))
     , Data.List.Relation.Unary.All.Properties.++⁺ f₁ f₂ , xa₂

-- Signatures before the rest: the signatures' own entries, and the rest's.
sigs-split′ : ∀ {al} (sigs rest : List Decl) {es} → All IsSig sigs → XAlign al (sigs ++ rest) es
            → Σ[ fs ∈ List Entry ] Σ[ es′ ∈ List Entry ] (es ≡ fs Data.List.++ es′) × XAlign al sigs fs × XAlign al rest es′
sigs-split′ [] rest [] xa = [] , _ , refl , xa-nil , xa
sigs-split′ (DSignature x nothing T ∷ sigs) rest (is-sig ∷ as) (xa-sig ps xa) =
  let (fs , es′ , e , xs , xr) = sigs-split′ sigs rest as xa in _ ∷ fs , es′ , Relation.Binary.PropositionalEquality.cong (_ ∷_) e , xa-sig ps xs , xr
sigs-split′ (DSignature x (just o) T ∷ sigs) rest (is-sig ∷ as) (xa-isig ps xa) =
  let (fs , es′ , e , xs , xr) = sigs-split′ sigs rest as xa in _ ∷ fs , es′ , Relation.Binary.PropositionalEquality.cong (_ ∷_) e , xa-isig ps xs , xr

private
  case-errT : ∀ {A : Set} {e : String} {ty : LT.Type} → (String ⊎ LT.Type ∋ inj₁ e) ≡ inj₂ ty → A
  case-errT ()

-- A signature's reading succeeded: ground, at its extraction.
project-ok : ∀ al n T {ty} → projectSig al n T ≡ inj₂ ty
           → Σ[ g ∈ Ground T ] (isGround T ≡ inj₁ g) × (ty ≡ expandAliases al (extractGround T g))
project-ok al n T eq with isGround T in ig
... | inj₂ _ = case-errT eq
... | inj₁ g = g , refl , honest-ok eq
  where
    honest-ok : ∀ {mh ty} → Once.Parser.honestSig n (expandAliases al (extractGround T g)) mh ≡ inj₂ ty → ty ≡ expandAliases al (extractGround T g)
    honest-ok {just _} refl = refl
    honest-ok {nothing} ()
