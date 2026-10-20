-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Polys — the resolver's polymorphic definitions are
-- the extractor's telescope entries (plan 0.121 §3.6, F6).
--
-- The resolver keeps a reference to a polymorphic definition bare; it reads
-- which definitions are polymorphic off the declarations as written
-- (`polyDefNames`), with the extractor's own classification (`isGround`,
-- then `isConcrete?`). The extractor reads the resolved declarations, the
-- signatures moved first. On a module whose type signatures each precede
-- their definition (`sigsAdjacent`, R10), the two agree: `polyDefNames` is
-- the names of the telescope entries (`ps-entries`). So an entry is
-- polymorphic exactly when its name is one of them (`kinds-of`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Polys where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Function using (_∋_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Once.Lang.Type.Poly using (extractGround)
open import Once.Type using (isGround)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; mkImport)
open import Once.Parser.Module.Resolve using (pdn-go; polyDefNames; signaturesWithOwner)
import Once.Parser as Parser
open Parser.FunInfo using (funName; funIsPrimitive)
open Parser.PolyFunInfo using (pfunName)
import Once.Lang.Resolution as LR
import Data.List.Relation.Unary.All as All
open import Data.Product using (Σ-syntax)
open import Once.Adequacy.SpecFront.Extract
  using (IsSig; is-sig; XAlign; xa-nil; xa-pass; xa-mono; xa-poly; xa-nosig; xa-sig; xa-isig; pa-alias; pa-import;
         SigReading; sr-mono; sr-open; sr-nonc)

-- The telescope entries' names.
polyNames : List Parser.Entry → List String
polyNames []                    = []
polyNames (Parser.e-poly p ∷ es) = pfunName p ∷ polyNames es
polyNames (Parser.e-fun _ ∷ es)  = polyNames es

------------------------------------------------------------------------
-- `sigsAdjacent`, as a relation
------------------------------------------------------------------------

data Other : Decl → Set where
  o-sig    : ∀ {n o t}   → Other (DSignature n o t)
  o-alias  : ∀ {n ps t}  → Other (DTypeAlias n ps t)
  o-import : ∀ {i}       → Other (DImport i)

-- a type signature, then its definition
data Adj : List Decl → Maybe String → Set where
  a-nil   : Adj [] nothing
  a-tsig  : ∀ {n t ds} → Adj ds (just n) → Adj (DTypeSig n t ∷ ds) nothing
  a-defP  : ∀ {n b ds} → Adj ds nothing → Adj (DFunDef n b ∷ ds) (just n)
  a-def   : ∀ {n b ds} → Adj ds nothing → Adj (DFunDef n b ∷ ds) nothing
  a-other : ∀ {d ds} → Other d → Adj ds nothing → Adj (d ∷ ds) nothing

private
  inj₁≢inj₂ : ∀ {s : String} → (String ⊎ ⊤ ∋ inj₁ s) ≡ inj₂ tt → ⊥
  inj₁≢inj₂ ()

  adj-def : ∀ s n b (d : Dec (s ≡ n)) ds → Parser.sigsAdjacent-def s n d ds ≡ inj₂ tt
          → (∀ p → Parser.sigsAdjacent ds p ≡ inj₂ tt → Adj ds p) → Adj (DFunDef n b ∷ ds) (just s)
  adj-def s .s b (yes refl) ds e rec = a-defP (rec nothing e)
  adj-def s n  b (no _)     ds e rec = ⊥-elim (inj₁≢inj₂ e)

adj-of : ∀ ds p → Parser.sigsAdjacent ds p ≡ inj₂ tt → Adj ds p
adj-of [] nothing e = a-nil
adj-of [] (just s) e = ⊥-elim (inj₁≢inj₂ e)
adj-of (DTypeSig n _ ∷ ds) nothing e = a-tsig (adj-of ds (just n) e)
adj-of (DTypeSig n _ ∷ ds) (just s) e = ⊥-elim (inj₁≢inj₂ e)
adj-of (DFunDef n _ ∷ ds) nothing e = a-def (adj-of ds nothing e)
adj-of (DFunDef n b ∷ ds) (just s) e = adj-def s n b (s ≟ n) ds e (adj-of ds)
adj-of (DSignature _ _ _ ∷ ds) nothing e = a-other o-sig (adj-of ds nothing e)
adj-of (DSignature _ _ _ ∷ ds) (just s) e = ⊥-elim (inj₁≢inj₂ e)
adj-of (DTypeAlias _ _ _ ∷ ds) nothing e = a-other o-alias (adj-of ds nothing e)
adj-of (DTypeAlias _ _ _ ∷ ds) (just s) e = ⊥-elim (inj₁≢inj₂ e)
adj-of (DImport _ ∷ ds) nothing e = a-other o-import (adj-of ds nothing e)
adj-of (DImport _ ∷ ds) (just s) e = ⊥-elim (inj₁≢inj₂ e)

------------------------------------------------------------------------
-- The written declarations and the resolved ones
------------------------------------------------------------------------

private
  pdn-owned : ∀ o ds rest → pdn-go (signaturesWithOwner o ds ++ rest) nothing ≡ pdn-go rest nothing
  pdn-owned o [] rest = refl
  pdn-owned o (DSignature _ _ _ ∷ ds) rest = pdn-owned o ds rest
  pdn-owned o (DTypeSig _ _ ∷ ds) rest = pdn-owned o ds rest
  pdn-owned o (DFunDef _ _ ∷ ds) rest = pdn-owned o ds rest
  pdn-owned o (DTypeAlias _ _ _ ∷ ds) rest = pdn-owned o ds rest
  pdn-owned o (DImport _ ∷ ds) rest = pdn-owned o ds rest

  adj-owned : ∀ o ds rest → Adj (signaturesWithOwner o ds ++ rest) nothing → Adj rest nothing
  adj-owned o [] rest a = a
  adj-owned o (DSignature _ _ _ ∷ ds) rest (a-other _ a) = adj-owned o ds rest a
  adj-owned o (DTypeSig _ _ ∷ ds) rest a = adj-owned o ds rest a
  adj-owned o (DFunDef _ _ ∷ ds) rest a = adj-owned o ds rest a
  adj-owned o (DTypeAlias _ _ _ ∷ ds) rest a = adj-owned o ds rest a
  adj-owned o (DImport _ ∷ ds) rest a = adj-owned o ds rest a

-- (mirrors `pdn-go`'s classification of a type signature)
pdn-res : ∀ {mm ps um am dsU dsR p} → LR.ResolvesDecls mm ps um am dsU dsR → Adj dsR p → pdn-go dsU p ≡ pdn-go dsR p
pdn-res LR.rds-nil a-nil = refl
pdn-res (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) (a-tsig {n} {t} a) with isGround t
... | inj₂ _ = cong (n ∷_) (pdn-res rds a)
... | inj₁ g with isConcrete? (extractGround t g)
...   | just _  = pdn-res rds a
...   | nothing = cong (n ∷_) (pdn-res rds a)
pdn-res (LR.rds-cons LR.nim-fundef (LR.rd-fundef _ _) rds) (a-defP a) = pdn-res rds a
pdn-res (LR.rds-cons LR.nim-fundef (LR.rd-fundef _ _) rds) (a-def a) = pdn-res rds a
pdn-res (LR.rds-cons LR.nim-sig LR.rd-signature rds) (a-other _ a) = pdn-res rds a
pdn-res (LR.rds-cons LR.nim-alias LR.rd-typealias rds) (a-other _ a) = pdn-res rds a
pdn-res (LR.rds-import {imp = mkImport p (just x)} {impDs = impDs} {ds' = dsR′} _ rds) (a-other _ a) =
  trans (pdn-res rds (adj-owned _ impDs dsR′ a)) (sym (pdn-owned _ impDs dsR′))
pdn-res (LR.rds-import {imp = mkImport p nothing} {impDs = impDs} {ds' = dsR′} _ rds) (a-other _ a) =
  trans (pdn-res rds (adj-owned _ impDs dsR′ a)) (sym (pdn-owned _ impDs dsR′))

------------------------------------------------------------------------
-- The resolved declarations and the entries
------------------------------------------------------------------------

private
  -- a ground, concrete signature: a monomorphic definition, not kept bare
  pdn-mono : ∀ {n t rest g} → isGround t ≡ inj₁ g → ∀ {c} → isConcrete? (extractGround t g) ≡ just c
           → pdn-go (DTypeSig n t ∷ rest) nothing ≡ pdn-go rest (just n)
  pdn-mono {n} {t} {rest} {g} ig ic with isGround t | ig
  ... | .(inj₁ g) | refl with isConcrete? (extractGround t g) | ic
  ...   | .(just _) | refl = refl

  -- otherwise: kept bare
  pdn-poly : ∀ {al n t rest} → SigReading al t nothing → pdn-go (DTypeSig n t ∷ rest) nothing ≡ n ∷ pdn-go rest (just n)
  pdn-poly {n = n} {t} {rest} (sr-open {u} ig) with isGround t | ig
  ... | .(inj₂ u) | refl = refl
  pdn-poly {n = n} {t} {rest} (sr-nonc g ig ic) with isGround t | ig
  ... | .(inj₁ g) | refl with isConcrete? (extractGround t g) | ic
  ...   | .nothing | refl = refl

  pdn-mono′ : ∀ {al n t rest ty} → SigReading al t (just ty) → pdn-go (DTypeSig n t ∷ rest) nothing ≡ pdn-go rest (just n)
  pdn-mono′ (sr-mono g c ig ic) = pdn-mono ig ic

pdn-xa : ∀ {al ds es} → Adj ds nothing → XAlign al (Parser.nonSigs ds) es → pdn-go ds nothing ≡ polyNames es
pdn-xa a-nil xa-nil = refl
pdn-xa (a-tsig (a-defP a)) (xa-mono sr xa) = trans (pdn-mono′ sr) (pdn-xa a xa)
pdn-xa (a-tsig (a-defP a)) (xa-poly sr xa) = trans (pdn-poly sr) (cong (_ ∷_) (pdn-xa a xa))
pdn-xa (a-def a) (xa-nosig xa) = pdn-xa a xa
pdn-xa (a-other o-sig a) xa = pdn-xa a xa
pdn-xa (a-other o-alias a) (xa-pass _ xa) = pdn-xa a xa
pdn-xa (a-other o-import a) (xa-pass _ xa) = pdn-xa a xa

------------------------------------------------------------------------
-- The entries' kinds
------------------------------------------------------------------------

-- An entry past the signatures: a definition (not an FFI declaration).
data DefEntry : Parser.Entry → Set where
  de-fun  : ∀ {fi} → funIsPrimitive fi ≡ false → DefEntry (Parser.e-fun fi)
  de-poly : ∀ {pfi} → DefEntry (Parser.e-poly pfi)

defs-of : ∀ {al ds es} → All (λ d → ¬ IsSig d) ds → XAlign al ds es → All DefEntry es
defs-of [] xa-nil = []
defs-of (_ ∷ n) (xa-pass _ xa) = defs-of n xa
defs-of (_ ∷ _ ∷ n) (xa-mono _ xa) = de-fun refl ∷ defs-of n xa
defs-of (_ ∷ _ ∷ n) (xa-poly _ xa) = de-poly ∷ defs-of n xa
defs-of (_ ∷ n) (xa-nosig xa) = de-fun refl ∷ defs-of n xa
defs-of (n ∷ _) (xa-sig _ _) = ⊥-elim (n is-sig)
defs-of (n ∷ _) (xa-isig _ _) = ⊥-elim (n is-sig)

-- An entry's kind: a definition, polymorphic exactly when one of `ps`.
EntryKind : List String → Parser.Entry → Set
EntryKind ps (Parser.e-fun fi)   = (funIsPrimitive fi ≡ false) × ¬ (funName fi ∈ ps)
EntryKind ps (Parser.e-poly pfi) = pfunName pfi ∈ ps

private
  poly-in : ∀ {pfi} es → Parser.e-poly pfi ∈ es → pfunName pfi ∈ polyNames es
  poly-in (Parser.e-poly _ ∷ es) (here refl) = here refl
  poly-in (Parser.e-poly _ ∷ es) (there m)   = there (poly-in es m)
  poly-in (Parser.e-fun _ ∷ es)  (there m)   = poly-in es m

  poly-mem : ∀ {n} es → n ∈ polyNames es → Σ[ pfi ∈ Parser.PolyFunInfo ] (Parser.e-poly pfi ∈ es) × (pfunName pfi ≡ n)
  poly-mem (Parser.e-poly p ∷ es) (here refl) = p , here refl , refl
  poly-mem (Parser.e-poly p ∷ es) (there m) = let (q , mq , e) = poly-mem es m in q , there mq , e
  poly-mem (Parser.e-fun _ ∷ es) m = let (q , mq , e) = poly-mem es m in q , there mq , e

  not-in : ∀ {x : String} {xs : List Parser.Entry} → All (x ≢_) (map Parser.entryNameOf xs) → ∀ {y} → y ∈ xs → x ≢ Parser.entryNameOf y
  not-in (n ∷ _) (here refl) = n
  not-in (_ ∷ a) (there m)   = not-in a m

  -- distinct names: an entry is the one of its name
  one-of : ∀ {xs : List Parser.Entry} → AllPairs _≢_ (map Parser.entryNameOf xs) → ∀ {x y} → x ∈ xs → y ∈ xs
         → Parser.entryNameOf x ≡ Parser.entryNameOf y → x ≡ y
  one-of (_ ∷ _) (here refl) (here refl) _ = refl
  one-of (h ∷ _) (here refl) (there m)   e = ⊥-elim (not-in h m e)
  one-of (h ∷ _) (there m)   (here refl) e = ⊥-elim (not-in h m (sym e))
  one-of (_ ∷ u) (there m)   (there m′)  e = one-of u m m′ e

  fun≢poly : ∀ {fi pfi} → Parser.e-fun fi ≢ Parser.e-poly pfi
  fun≢poly ()

kinds-of : ∀ es → AllPairs _≢_ (map Parser.entryNameOf es) → All DefEntry es → All (EntryKind (polyNames es)) es
kinds-of es u de = All.tabulate at
  where
    at : ∀ {e} → e ∈ es → EntryKind (polyNames es) e
    at {Parser.e-poly pfi} m = poly-in es m
    at {Parser.e-fun fi} m with All.lookup de m
    ... | de-fun ep = ep , λ n → let (q , mq , e) = poly-mem es n in fun≢poly (one-of u m mq (sym e))
