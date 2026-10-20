-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Prim — the compiler's literals and primitive
-- operations as the Spec's (plan 0.121, the core bridge): the same, name for
-- name, at the same types.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Lang.Contract using (ISig)
import Once.Lang.Core.PolyTy as LP

module Once.Adequacy.SpecCore.Prim {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Lang.Core.Syntax S as L
open import Once.Adequacy.SpecCore.Schema using (ptyS)

litS : L.Lit → SC.Lit
litS (L.lit-int i)   = SC.lit-int i
litS (L.lit-float d) = SC.lit-float d

primS : L.Prim → SC.Prim
primS L.p-add  = SC.p-add
primS L.p-sub  = SC.p-sub
primS L.p-mul  = SC.p-mul
primS L.p-div  = SC.p-div
primS L.p-mod  = SC.p-mod
primS L.p-neg  = SC.p-neg
primS L.p-lt   = SC.p-lt
primS L.p-le   = SC.p-le
primS L.p-gt   = SC.p-gt
primS L.p-ge   = SC.p-ge
primS L.p-eq   = SC.p-eq
primS L.p-ne   = SC.p-ne
primS L.p-fadd = SC.p-fadd
primS L.p-fsub = SC.p-fsub
primS L.p-fmul = SC.p-fmul
primS L.p-fdiv = SC.p-fdiv
primS L.p-i2f  = SC.p-i2f

-- (the types, over any type variables)
module _ {m : ℕ} where

  primDom-S : ∀ p → ptyS (LP.⌈_⌉ {m} (L.primDom p)) ≡ SC.primDom (primS p)
  primDom-S L.p-add  = refl
  primDom-S L.p-sub  = refl
  primDom-S L.p-mul  = refl
  primDom-S L.p-div  = refl
  primDom-S L.p-mod  = refl
  primDom-S L.p-neg  = refl
  primDom-S L.p-lt   = refl
  primDom-S L.p-le   = refl
  primDom-S L.p-gt   = refl
  primDom-S L.p-ge   = refl
  primDom-S L.p-eq   = refl
  primDom-S L.p-ne   = refl
  primDom-S L.p-fadd = refl
  primDom-S L.p-fsub = refl
  primDom-S L.p-fmul = refl
  primDom-S L.p-fdiv = refl
  primDom-S L.p-i2f  = refl

  primCod-S : ∀ p → ptyS (LP.⌈_⌉ {m} (L.primCod p)) ≡ SC.primCod (primS p)
  primCod-S L.p-add  = refl
  primCod-S L.p-sub  = refl
  primCod-S L.p-mul  = refl
  primCod-S L.p-div  = refl
  primCod-S L.p-mod  = refl
  primCod-S L.p-neg  = refl
  primCod-S L.p-lt   = refl
  primCod-S L.p-le   = refl
  primCod-S L.p-gt   = refl
  primCod-S L.p-ge   = refl
  primCod-S L.p-eq   = refl
  primCod-S L.p-ne   = refl
  primCod-S L.p-fadd = refl
  primCod-S L.p-fsub = refl
  primCod-S L.p-fmul = refl
  primCod-S L.p-fdiv = refl
  primCod-S L.p-i2f  = refl
