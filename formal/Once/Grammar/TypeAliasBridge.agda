-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.TypeAliasBridge — independent relational spec for the TYPE ALIAS
-- declaration parser + sound/complete bridge. Bottoms at
-- the proven `ParsesType` island (`Once.Grammar.ParserBridge`).
------------------------------------------------------------------------

module Once.Grammar.TypeAliasBridge where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <-≤-trans)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _,_; ∃; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (anyWordB; ParseAtB; Decl; DTypeAlias; parseTypeB-adapt)
open import Once.Parser.Module.DeclTail
  using (goTypeAliasB; goTypeAliasWF; gta-aw; gta-eq; gta-type; gta-sub;
         parseTypeAliasB; pta-aw; pta-go; taEqHead; taDrop1; taDrop1-≤)
open import Once.Parser.TypeRelation using (ParsesType)
open import Once.Spec.Grammar.TypeAlias
  using (ParsesTypeAlias; gta-eq-r; gta-word-r; ParsesTypeAliasDecl; pta-mk)
open import Once.Parser.Type using (parseTypeWF)
open import Once.Grammar.ParserBridge using (complete-typeWFraw)
open import Once.Parser.Module.Core using (wordHead)
open import Once.Grammar.ImportBridge using (anyWordB-inv; ij-false)

------------------------------------------------------------------------
-- Param scanner `param* = Type` (params accumulator). Bottoms at `ParsesType`.
------------------------------------------------------------------------

-- The relation is in `Once.Spec.Grammar.TypeAlias` (plan 0.84).

sound-gtaWF : ∀ (name : String) (toks : List Token) (params : List String) (a : Acc _<_ (length toks))
  {d rest bnd} → goTypeAliasWF name toks params a ≡ just (d , rest , bnd) →
  ParsesTypeAlias name params toks d rest
sound-gtaWF name toks params (acc rec) h with anyWordB toks in aw
... | just (p , rest' , bnd) with anyWordB-inv aw
...   | refl with goTypeAliasWF name rest' (p ∷ params) (rec bnd) in subeq
...     | nothing with () ← h
...     | just (d , rest'' , bnd') with refl ← just-injective h =
          gta-word-r (sound-gtaWF name rest' (p ∷ params) (rec bnd) subeq)
sound-gtaWF name toks params (acc rec) h | nothing with taEqHead toks in eh
... | false with () ← h
... | true with parseTypeWF (taDrop1 toks) (<-wellFounded (length (taDrop1 toks))) in subeq
...   | nothing with () ← h
...   | just (ty , rest'' , d) with refl ← just-injective h = gta-eq-r (cong is-just aw) eh d

sound-gta : ∀ (name : String) (toks : List Token) (params : List String) {d rest bnd} →
  goTypeAliasB name toks params ≡ just (d , rest , bnd) → ParsesTypeAlias name params toks d rest
sound-gta name toks params h = sound-gtaWF name toks params (<-wellFounded (length toks)) h

complete-gtaWF : ∀ {name params toks d rest} (a : Acc _<_ (length toks)) →
  ParsesTypeAlias name params toks d rest →
  Σ[ bnd ∈ (length rest < length toks) ] goTypeAliasWF name toks params a ≡ just (d , rest , bnd)
complete-gtaWF (acc rec) (gta-eq-r {params} {toks} wf eh pt) rewrite ij-false wf | eh
  with complete-typeWFraw pt (<-wellFounded (length (taDrop1 toks)))
... | (d' , eqd) rewrite eqd = _ , refl
complete-gtaWF (acc rec) (gta-word-r {params} {p} {rest'} sub)
  with complete-gtaWF (rec (s≤s ≤-refl)) sub
... | (bnd' , eqr) rewrite eqr = _ , refl

complete-gta : ∀ {name params toks d rest} → ParsesTypeAlias name params toks d rest →
  Σ[ bnd ∈ (length rest < length toks) ] goTypeAliasB name toks params ≡ just (d , rest , bnd)
complete-gta {toks = toks} d = complete-gtaWF (<-wellFounded (length toks)) d

------------------------------------------------------------------------
-- `type Name param* = Type` (consume the alias name, then the scanner).
------------------------------------------------------------------------

-- The relation is in `Once.Spec.Grammar.TypeAlias` (plan 0.84).

sound-typealias : ∀ {toks d rest bnd} → parseTypeAliasB toks ≡ just (d , rest , bnd) →
  ParsesTypeAliasDecl toks d rest
sound-typealias {toks} h with anyWordB toks in aw
... | nothing with () ← h
... | just (name , rest , bnd) with anyWordB-inv aw
...   | refl with goTypeAliasB name rest [] in geq
...     | nothing with () ← h
...     | just (d , rest' , bnd') with refl ← just-injective h = pta-mk (sound-gta name rest [] geq)

complete-typealias : ∀ {toks d rest} → ParsesTypeAliasDecl toks d rest →
  Σ[ bnd ∈ (length rest < length toks) ] parseTypeAliasB toks ≡ just (d , rest , bnd)
complete-typealias (pta-mk {name} {rest} gta) with complete-gta gta
... | (bnd' , eq) rewrite eq = _ , refl
