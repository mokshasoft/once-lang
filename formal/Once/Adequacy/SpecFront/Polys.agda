-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Polys — the extractor's telescope entries and
-- their kinds (plan 0.121 §3.6, F6).
--
-- The telescope entries' names (`polyNames`): an entry is polymorphic exactly
-- when its name is one of them (`kinds-of`). And a type signature
-- immediately followed by its definition (`Adj`, the extractor's
-- `sigsAdjacent`, R10).
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

open import Once.Internal.Type.Poly using (extractGround)
open import Once.Type using (isGround)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Spec.Surface.Syntax using (mkImport)
import Once.Parser as Parser
open Parser.FunInfo using (funName; funIsPrimitive)
open Parser.PolyFunInfo using (pfunName)
import Once.Internal.Resolution as LR
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

-- (each an entry's name)
poly-names : ∀ {x} es → x ∈ polyNames es → x ∈ map Parser.entryNameOf es
poly-names (Parser.e-poly _ ∷ es) (here refl) = here refl
poly-names (Parser.e-poly _ ∷ es) (there m)   = there (poly-names es m)
poly-names (Parser.e-fun _ ∷ es)  m           = there (poly-names es m)

------------------------------------------------------------------------
-- `sigsAdjacent`, as a relation
------------------------------------------------------------------------

-- Each type signature immediately followed by its definition.
data NotTSig : Decl → Set where
  nt-def    : ∀ {x b}       → NotTSig (DFunDef x b)
  nt-sig    : ∀ {x o T}     → NotTSig (DSignature x o T)
  nt-alias  : ∀ {x ps′ t}   → NotTSig (DTypeAlias x ps′ t)
  nt-import : ∀ {i}         → NotTSig (DImport i)

data Adj : List Decl → Set where
  adj-nil   : Adj []
  adj-sig   : ∀ {x T b ds} → Adj ds → Adj (DTypeSig x T ∷ DFunDef x b ∷ ds)
  adj-other : ∀ {d ds} → NotTSig d → Adj ds → Adj (d ∷ ds)

-- The extractor's check gives it.
mutual
  adj-of : ∀ ds → Parser.sigsAdjacent ds nothing ≡ inj₂ tt → Adj ds
  adj-of [] _ = adj-nil
  adj-of (DTypeSig n _ ∷ ds) e = adj-pend n ds e
  adj-of (DFunDef n _ ∷ ds) e = adj-other nt-def (adj-of ds e)
  adj-of (DSignature _ _ _ ∷ ds) e = adj-other nt-sig (adj-of ds e)
  adj-of (DTypeAlias _ _ _ ∷ ds) e = adj-other nt-alias (adj-of ds e)
  adj-of (DImport _ ∷ ds) e = adj-other nt-import (adj-of ds e)

  adj-pend : ∀ {T} s ds → Parser.sigsAdjacent ds (just s) ≡ inj₂ tt → Adj (DTypeSig s T ∷ ds)
  adj-pend s [] ()
  adj-pend s (DTypeSig _ _ ∷ ds) ()
  adj-pend s (DFunDef n b ∷ ds) e = adj-def s n b ds (s ≟ n) e
  adj-pend s (DSignature _ _ _ ∷ ds) ()
  adj-pend s (DTypeAlias _ _ _ ∷ ds) ()
  adj-pend s (DImport _ ∷ ds) ()

  adj-def : ∀ {T} s n b ds (d : Dec (s ≡ n)) → Parser.sigsAdjacent-def s n d ds ≡ inj₂ tt → Adj (DTypeSig s T ∷ DFunDef n b ∷ ds)
  adj-def s .s b ds (yes refl) e = adj-sig (adj-of ds e)
  adj-def s n b ds (no _) ()

------------------------------------------------------------------------
-- The entries' kinds
------------------------------------------------------------------------

-- An entry past the signatures: a definition (not an FFI declaration).
data DefEntry : Parser.Entry → Set where
  de-fun  : ∀ {fi} → funIsPrimitive fi ≡ false → DefEntry (Parser.e-fun fi)
  de-poly : ∀ {pfi} → DefEntry (Parser.e-poly pfi)

defs-of : ∀ {ds es} → All (λ d → ¬ IsSig d) ds → XAlign ds es → All DefEntry es
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

-- a definition is not named as a telescope entry
poly-not-fun : ∀ es → AllPairs _≢_ (map Parser.entryNameOf es) → ∀ {fi} → Parser.e-fun fi ∈ es → ¬ (funName fi ∈ polyNames es)
poly-not-fun es u m n = let (q , mq , e) = poly-mem es n in fun≢poly (one-of u m mq (sym e))

kinds-of : ∀ es → AllPairs _≢_ (map Parser.entryNameOf es) → All DefEntry es → All (EntryKind (polyNames es)) es
kinds-of es u de = All.tabulate at
  where
    at : ∀ {e} → e ∈ es → EntryKind (polyNames es) e
    at {Parser.e-poly pfi} m = poly-in es m
    at {Parser.e-fun fi} m with All.lookup de m
    ... | de-fun ep = ep , λ n → let (q , mq , e) = poly-mem es n in fun≢poly (one-of u m mq (sym e))
