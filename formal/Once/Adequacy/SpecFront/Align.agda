-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Align — the Spec's resolved declarations against
-- the compiler's entries (plan 0.121 §3.6, F6).
--
-- The Spec walks a module's resolved declarations in place; the compiler
-- reads its resolved declarations into entries, the `signature`s first
-- (`sigsFirst`), the definitions after (`Extract.XAlign` of `nonSigs`). Given
-- the two declaration lists related one by one (`DR`: a definition's body by
-- `RX`, a type signature by its reading, an own signature, an import followed
-- by its module's signatures, an alias) and each compiler type signature
-- followed by its definition (`Adj`, the extractor's check), the definitions'
-- entries are aligned with the Spec's declarations as the walk needs
-- (`Align`, `align-of`).
------------------------------------------------------------------------

open import Data.List using (List)
open import Data.String using (String)
open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecFront.Align (Σ : Signature) where

open import Once.Adequacy.SpecFront.Polys using (Adj; adj-nil; adj-sig; adj-other)

open import Data.List using ([]; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; sym; trans)

import Once.Internal.Type as LT
import Once.Internal.Type.WellFormed as LW
open import Once.Type.Rigid using (extractGround-rf)
open import Once.TypeCheck.DeciderComplete using (isGround-complete-at; Ground-irrelevant)
open import Once.Functor.Decide using (isConcrete?)
import Data.Sum
open import Once.Internal.Type.Poly using (PolyType; PTVar; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ-type; Pν-type;
  PolyFunctor; PK; PId; _P⊕_; _P⊗_; Ground; GroundF; extractGround; extractGroundF)
import Once.Internal.Core.PolyTy as LP
import Once.Spec.Surface.Syntax as SX
open import Once.Spec.Surface.Program
  using (SchemaOf; TypeOf; FunOf; NotDefinition; nd-sig; nd-alias; nd-import;
         to-unit; to-void; to-int; to-float; to-*; to-+; to-⇒; to-act; to-eff; to-μ; to-ν; fo-K; fo-Id; fo-⊕; fo-⊗)
open import Once.Parser.Module.Core using (Decl; DTypeAlias; DTypeSig; DFunDef; DSignature; DImport)
open import Once.Parser.TypeAlias using (TypeAliasEnv; expandAliases; expandAliasesF)
import Once.Parser as Parser
open import Once.Internal.Core.Schema using (schemaOf)
open import Once.Internal.Core.Translate using (monoSchema)
open import Once.Adequacy.SpecGrammar.Conv using (toPoly; toPolyF)
open import Once.Adequacy.SpecCore.Schema using (schS; ptyS; pfunS)
open import Once.Adequacy.SpecFront.Expr using (RX)
open import Once.Adequacy.SpecFront.SchemaOf using (schemaOf-S)
open import Once.Adequacy.SpecFront.Extract using (XAlign; xa-nil; xa-pass; xa-mono; xa-poly; xa-nosig; xa-sig; xa-isig;
  pa-alias; pa-import; SigReading; sr-mono; sr-open; sr-nonc)

------------------------------------------------------------------------
-- What the walk is given
------------------------------------------------------------------------

-- Why a signature makes a telescope definition: no ground reading of it is
-- concrete.
NotMono : PolyType → Set
NotMono T = ∀ (g : Ground T) → isConcrete? (extractGround T g) ≡ nothing

-- A definition with a signature (monomorphic or telescope), one without, and
-- the other declarations skipped; each body related.
data Align : List SX.Decl → List Parser.Entry → Set where
  al-nil   : Align [] []
  al-skip  : ∀ {d ds es} → NotDefinition Σ d → Align ds es → Align (d ∷ ds) es
  al-mono  : ∀ {x T′ e e′ ty ds es} → SchemaOf T′ (schS (monoSchema ty)) → LW.RigidFree ty → RX [] e e′ → Align ds es
           → Align (SX.DTypeSig x T′ ∷ SX.DFunDef x e′ ∷ ds) (Parser.e-fun (Parser.mkFunInfo x (just ty) e false) ∷ es)
  al-nosig : ∀ {x e e′ ds es} → RX [] e e′ → Align ds es
           → Align (SX.DFunDef x e′ ∷ ds) (Parser.e-fun (Parser.mkFunInfo x nothing e false) ∷ es)
  al-poly  : ∀ {x T e e′ ds es} → SchemaOf (toPoly T) (schS (schemaOf T)) → NotMono T → RX [] e e′ → Align ds es
           → Align (SX.DTypeSig x (toPoly T) ∷ SX.DFunDef x e′ ∷ ds) (Parser.e-poly (Parser.mkPolyFunInfo x T e) ∷ es)

------------------------------------------------------------------------
-- The two resolved declaration lists
------------------------------------------------------------------------

-- Imported signatures, owned by the importing site.
ImportedSig : Decl → Set
ImportedSig d = Σ[ x ∈ String ] Σ[ o ∈ List String ] Σ[ T ∈ PolyType ] d ≡ DSignature x (just o) T

data DR : List SX.Decl → List Decl → Set where
  dr-nil    : DR [] []
  dr-tsig   : ∀ {x T ds dc} → DR ds dc → DR (SX.DTypeSig x (toPoly T) ∷ ds) (DTypeSig x T ∷ dc)
  dr-def    : ∀ {x e e′ ds dc} → RX [] e e′ → DR ds dc → DR (SX.DFunDef x e′ ∷ ds) (DFunDef x e ∷ dc)
  dr-sig    : ∀ {x T′ T ds dc} → DR ds dc → DR (SX.DSignature x T′ ∷ ds) (DSignature x nothing T ∷ dc)
  dr-import : ∀ {i i′ sigs ds dc} → All ImportedSig sigs → DR ds dc → DR (SX.DImport i′ ∷ ds) (DImport i ∷ sigs ++ dc)
  dr-alias  : ∀ {x ps′ t x′ ps″ t′ ds dc} → DR ds dc → DR (SX.DTypeAlias x′ ps″ t′ ∷ ds) (DTypeAlias x ps′ t ∷ dc)

------------------------------------------------------------------------
-- A ground signature's schema
------------------------------------------------------------------------

mutual
  expand-id : ∀ al (A : LT.Type) → expandAliases al A ≡ A
  expand-id al LT.Unit        = refl
  expand-id al LT.Void        = refl
  expand-id al LT.Int         = refl
  expand-id al LT.Float       = refl
  expand-id al (LT.rigid k i) = refl
  expand-id al (a LT.* b)     = cong₂ LT._*_ (expand-id al a) (expand-id al b)
  expand-id al (a LT.+ b)     = cong₂ LT._+_ (expand-id al a) (expand-id al b)
  expand-id al (a LT.⇒[ k ] b) = cong₂ (λ x y → x LT.⇒[ k ] y) (expand-id al a) (expand-id al b)
  expand-id al (LT.μ-type F)   = cong LT.μ-type (expandF-id al F)
  expand-id al (LT.ν-type F π) = cong (λ G → LT.ν-type G π) (expandF-id al F)

  expandF-id : ∀ al (F : LT.Functor) → expandAliasesF al F ≡ F
  expandF-id al (LT.K A)   = cong LT.K (expand-id al A)
  expandF-id al LT.Id      = refl
  expandF-id al (F LT.⊕ G) = cong₂ LT._⊕_ (expandF-id al F) (expandF-id al G)
  expandF-id al (F LT.⊗ G) = cong₂ LT._⊗_ (expandF-id al F) (expandF-id al G)

private
  fin0 : Fin 0 → ⊥
  fin0 ()

  no-names : Fin 0 → String
  no-names ()

  mutual
    reads-ground : ∀ (T : PolyType) (g : Ground T) → TypeOf no-names (toPoly T) (ptyS (LP.⌈_⌉ {0} (extractGround T g)))
    reads-ground PUnit _  = to-unit
    reads-ground PVoid _  = to-void
    reads-ground PInt _   = to-int
    reads-ground PFloat _ = to-float
    reads-ground (PTVar _) ()
    reads-ground (A P* B) (ga , gb) = to-* (reads-ground A ga) (reads-ground B gb)
    reads-ground (A P+ B) (ga , gb) = to-+ (reads-ground A ga) (reads-ground B gb)
    reads-ground (A P⇒[ q ] B) (ga , gb) = to-⇒ (reads-ground A ga) (reads-ground B gb)
    reads-ground (PEff A B) (ga , gb) = to-eff (reads-ground A ga) (reads-ground B gb)
    reads-ground (PAct A B) (ga , gb) = to-act (reads-ground A ga) (reads-ground B gb)
    reads-ground (Pμ-type F) g = to-μ (readsF-ground F g)
    reads-ground (Pν-type F φ) g = to-ν (readsF-ground F g)

    readsF-ground : ∀ (F : PolyFunctor) (g : GroundF F) → FunOf no-names (toPolyF F) (Once.Adequacy.SpecCore.Schema.pfunS (LP.⌈_⌉F {0} (extractGroundF F g)))
    readsF-ground (PK A) g = fo-K (reads-ground A g)
    readsF-ground PId _ = fo-Id
    readsF-ground (F P⊕ G) (gf , gg) = fo-⊕ (readsF-ground F gf) (readsF-ground G gg)
    readsF-ground (F P⊗ G) (gf , gg) = fo-⊗ (readsF-ground F gf) (readsF-ground G gg)

-- A ground signature, read by the Spec, is the monomorphic entry's schema.
ground-schemaOf : ∀ al (T : PolyType) (g : Ground T) → SchemaOf (toPoly T) (schS (monoSchema (expandAliases al (extractGround T g))))
ground-schemaOf al T g =
  subst (λ ty → SchemaOf (toPoly T) (schS (monoSchema ty))) (sym (expand-id al (extractGround T g)))
    (record { names = no-names ; distinct = λ {i} → ⊥-elim (fin0 i) ; reads = reads-ground T g
            ; used = λ i → ⊥-elim (fin0 i) ; kinded = λ i → ⊥-elim (fin0 i) })

------------------------------------------------------------------------
-- The alignment
------------------------------------------------------------------------

private
  nonSigs-imported : ∀ (sigs dc : List Decl) → All ImportedSig sigs → Parser.nonSigs (sigs ++ dc) ≡ Parser.nonSigs dc
  nonSigs-imported []          dc []                       = refl
  nonSigs-imported (_ ∷ sigs)  dc ((x , o , T , refl) ∷ as) = nonSigs-imported sigs dc as

  -- the reading's schema
  mono-schema : ∀ {al T ty} → SigReading al T (just ty) → SchemaOf (toPoly T) (schS (monoSchema ty))
  mono-schema {al} {T} (sr-mono g c _ _) = ground-schemaOf al T g

  poly-why : ∀ {al T} → SigReading al T nothing → NotMono T
  poly-why {T = T} (sr-open ig) g = ⊥-elim (inj≢ (trans (sym (isGround-complete-at T g)) ig))
    where
      inj≢ : ∀ {A B : Set} {a : A} {b : B} → _≡_ {A = A Data.Sum.⊎ B} (inj₁ a) (inj₂ b) → ⊥
      inj≢ ()
  poly-why {T = T} (sr-nonc g₀ ig ic) g = subst (λ h → isConcrete? (extractGround T h) ≡ nothing) (Ground-irrelevant T g₀ g) ic

  mono-rf : ∀ {al T ty} → SigReading al T (just ty) → LW.RigidFree ty
  mono-rf {al} {T} (sr-mono g c _ _) = subst LW.RigidFree (sym (expand-id al (extractGround T g))) (extractGround-rf T g)

align-of : ∀ {al ds dc es} → DR ds dc → Adj dc → XAlign al (Parser.nonSigs dc) es → Align ds es
align-of dr-nil adj-nil xa-nil = al-nil
align-of (dr-sig r) (adj-other _ a) xa = al-skip nd-sig (align-of r a xa)
align-of {al} (dr-import {sigs = sigs} {dc = dc} as r) (adj-other _ a) (xa-pass pa-import xa) =
  al-skip nd-import (align-of r (adj-rest sigs as a) (subst (λ l → XAlign al l _) (nonSigs-imported sigs dc as) xa))
  where
    adj-rest : ∀ (sigs : List Decl) {dc} → All ImportedSig sigs → Adj (sigs ++ dc) → Adj dc
    adj-rest []         []                       a′ = a′
    adj-rest (_ ∷ sigs) ((x , o , T , refl) ∷ as′) (adj-other _ a′) = adj-rest sigs as′ a′
align-of (dr-alias r) (adj-other _ a) (xa-pass pa-alias xa) = al-skip nd-alias (align-of r a xa)
align-of (dr-def rx r) (adj-other _ a) (xa-nosig xa) = al-nosig rx (align-of r a xa)
align-of (dr-tsig (dr-def rx r)) (adj-sig a) (xa-mono sr xa) = al-mono (mono-schema sr) (mono-rf sr) rx (align-of r a xa)
align-of (dr-tsig {T = T} (dr-def rx r)) (adj-sig a) (xa-poly sr xa) = al-poly (schemaOf-S T) (poly-why sr) rx (align-of r a xa)
align-of (dr-tsig r) (adj-other () a) xa
