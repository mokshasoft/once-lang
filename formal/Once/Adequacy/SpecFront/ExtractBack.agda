-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.ExtractBack — the extractor succeeds on what the
-- Spec reads (plan 0.121 `complete`; the converse of `Extract`).
--
-- `XAlign` says, declaration by declaration, what the extractor produces;
-- conversely, whatever `XAlign` describes the extractor produces
-- (`align-extract`). A module whose type signatures each precede their
-- definition (`Adj`) passes `sigsAdjacent` (`adj-ok`).
--
-- (The extractor is written with `with`; the proof follows it.)
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.ExtractBack where

import Once.Internal.Type.Poly
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Surface.Syntax using (RVar)
open import Once.Parser.Module.Core using (Decl; DTypeAlias; DTypeSig; DFunDef; DSignature; DImport)
open import Once.Parser
  using (Entry; e-fun; e-poly; mkFunInfo; mkPolyFunInfo; extractFunctions-go; sigsAdjacent; sigsAdjacent-def)
open import Once.Adequacy.SpecFront.Extract
  using (XAlign; xa-nil; xa-pass; xa-mono; xa-poly; xa-nosig; xa-sig; xa-isig; pa-alias; pa-import;
         SigReading; sr-mono; sr-open; sr-nonc)
open import Once.Adequacy.SpecFront.Polys using (Adj; adj-nil; adj-sig; adj-other; nt-def; nt-sig; nt-alias; nt-import)

------------------------------------------------------------------------
-- What `XAlign` describes, the extractor produces
------------------------------------------------------------------------

align-extract : ∀ {ds es} → XAlign ds es → extractFunctions-go ds nothing ≡ inj₂ es
align-extract xa-nil = refl
align-extract (xa-pass pa-alias xa)  = align-extract xa
align-extract (xa-pass pa-import xa) = align-extract xa
align-extract (xa-mono {x = x} {T = T} {b = b} {ds = ds} (sr-mono g c ig ic) xa) rewrite ig | ic with x ≟ x
... | yes _  rewrite align-extract xa = refl
... | no x≢x = Data.Empty.⊥-elim (x≢x refl)
  where import Data.Empty
align-extract (xa-poly {x = x} (sr-open ig) xa) rewrite ig with x ≟ x
... | yes _  rewrite align-extract xa = refl
... | no x≢x = Data.Empty.⊥-elim (x≢x refl)
  where import Data.Empty
align-extract (xa-poly {x = x} (sr-nonc g ig ic) xa) rewrite ig | ic with x ≟ x
... | yes _  rewrite align-extract xa = refl
... | no x≢x = Data.Empty.⊥-elim (x≢x refl)
  where import Data.Empty
align-extract (xa-nosig xa) rewrite align-extract xa = refl
align-extract (xa-sig ps xa) rewrite ps | align-extract xa = refl
align-extract (xa-isig ps xa) rewrite ps | align-extract xa = refl

------------------------------------------------------------------------
-- Each type signature immediately before its definition: `sigsAdjacent`
------------------------------------------------------------------------

adj-ok : ∀ {ds} → Adj ds → sigsAdjacent ds nothing ≡ inj₂ tt
adj-ok adj-nil = refl
adj-ok (adj-sig {x = s} a) with s ≟ s
... | yes _  = adj-ok a
... | no s≢s = Data.Empty.⊥-elim (s≢s refl)
  where import Data.Empty
adj-ok (adj-other nt-def a)    = adj-ok a
adj-ok (adj-other nt-sig a)    = adj-ok a
adj-ok (adj-other nt-alias a)  = adj-ok a
adj-ok (adj-other nt-import a) = adj-ok a

------------------------------------------------------------------------
-- The Spec's walk: each type signature immediately before its definition
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary using (¬_)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
open import Once.Type using (isGround)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Spec.Signature using (Signature)
import Once.Spec.Surface.Syntax as S
import Once.Spec.Surface.Program as SPr
import Once.Parser as Parser
open import Once.Adequacy.SpecFront.Extract using (IsSig; is-sig)

data SNotTSig : S.Decl → Set where
  snt-def    : ∀ {x e}      → SNotTSig (S.DFunDef x e)
  snt-sig    : ∀ {x t}      → SNotTSig (S.DSignature x t)
  snt-alias  : ∀ {x ps t}   → SNotTSig (S.DTypeAlias x ps t)
  snt-import : ∀ {i}        → SNotTSig (S.DImport i)

data SAdj : List S.Decl → Set where
  sadj-nil   : SAdj []
  sadj-sig   : ∀ {x T e ds} → SAdj ds → SAdj (S.DTypeSig x T ∷ S.DFunDef x e ∷ ds)
  sadj-other : ∀ {d ds} → SNotTSig d → SAdj ds → SAdj (d ∷ ds)

walk-adj : ∀ {Σ s} {S₀ : _} {nm tl ds s′} {S′ : _} {nm′ tl′}
         → SPr.Walk Σ {s} S₀ nm tl ds {s′} S′ nm′ tl′ → SAdj ds
walk-adj SPr.w-end = sadj-nil
walk-adj (SPr.w-skip SPr.nd-sig w)    = sadj-other snt-sig (walk-adj w)
walk-adj (SPr.w-skip SPr.nd-alias w)  = sadj-other snt-alias (walk-adj w)
walk-adj (SPr.w-skip SPr.nd-import w) = sadj-other snt-import (walk-adj w)
walk-adj (SPr.w-sig _ _ _ w)          = sadj-sig (walk-adj w)
walk-adj (SPr.w-nosig _ _ _ w)        = sadj-other snt-def (walk-adj w)

module _ (Σ : Signature) where
  open import Once.Adequacy.SpecFront.Align Σ using (DR; dr-nil; dr-tsig; dr-def; dr-sig; dr-import; dr-alias; ImportedSig)

  private
    sigs-adj : ∀ {sigs dc} → All ImportedSig sigs → Adj dc → Adj (sigs ++ dc)
    sigs-adj []                          a = a
    sigs-adj ((_ , _ , _ , refl) ∷ ss) a = adj-other nt-sig (sigs-adj ss a)

  -- the compiler's resolved declarations keep the Spec's adjacency
  dr-adj : ∀ {ds dc} → DR ds dc → SAdj ds → Adj dc
  dr-adj dr-nil sadj-nil = adj-nil
  dr-adj (dr-tsig (dr-def _ dr)) (sadj-sig a) = adj-sig (dr-adj dr a)
  dr-adj (dr-def _ dr) (sadj-other snt-def a) = adj-other nt-def (dr-adj dr a)
  dr-adj (dr-sig dr) (sadj-other snt-sig a) = adj-other nt-sig (dr-adj dr a)
  dr-adj (dr-alias dr) (sadj-other snt-alias a) = adj-other nt-alias (dr-adj dr a)
  dr-adj (dr-import ss dr) (sadj-other snt-import a) = adj-other nt-import (sigs-adj ss (dr-adj dr a))

-- …and without the `signature` declarations
nonSigs-adj : ∀ {ds} → Adj ds → Adj (Parser.nonSigs ds)
nonSigs-adj adj-nil = adj-nil
nonSigs-adj (adj-sig a) = adj-sig (nonSigs-adj a)
nonSigs-adj (adj-other nt-def a)    = adj-other nt-def (nonSigs-adj a)
nonSigs-adj (adj-other nt-sig a)    = nonSigs-adj a
nonSigs-adj (adj-other nt-alias a)  = adj-other nt-alias (nonSigs-adj a)
nonSigs-adj (adj-other nt-import a) = adj-other nt-import (nonSigs-adj a)

------------------------------------------------------------------------
-- The definitions' entries
------------------------------------------------------------------------

-- A type signature always has a reading (mirrors the extractor's `with`).
sig-reading : ∀ (T : PolyType) → Σ[ m ∈ Maybe LT.Type ] SigReading T m
sig-reading T with isGround T in ig
... | inj₂ _ = nothing , sr-open ig
... | inj₁ g with isConcrete? (Once.Internal.Type.Poly.extractGround T g) in ic
...   | just c  = _ , sr-mono g c ig ic
...   | nothing = nothing , sr-nonc g ig ic

xalign-of : ∀ {ds} → Adj ds → All (λ d → ¬ IsSig d) ds → Σ[ es ∈ List Entry ] XAlign ds es
xalign-of adj-nil [] = [] , xa-nil
xalign-of (adj-sig {T = T} a) (_ ∷ _ ∷ ns) with sig-reading T | xalign-of a ns
... | just ty , sr  | es , xa = _ , xa-mono sr xa
... | nothing , sr  | es , xa = _ , xa-poly sr xa
xalign-of (adj-other nt-def a) (_ ∷ ns)    = let (es , xa) = xalign-of a ns in _ , xa-nosig xa
xalign-of (adj-other nt-sig a) (n ∷ ns)    = ⊥-elim (n is-sig)
xalign-of (adj-other nt-alias a) (_ ∷ ns)  = let (es , xa) = xalign-of a ns in _ , xa-pass pa-alias xa
xalign-of (adj-other nt-import a) (_ ∷ ns) = let (es , xa) = xalign-of a ns in _ , xa-pass pa-import xa
