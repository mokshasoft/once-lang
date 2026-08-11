------------------------------------------------------------------------
-- Theory.RanzowFixpoint.SelfEncoding
--
-- The MINIMAL interface the evaluator-form Ranzow correctness theorems
-- actually use: a carrier with composition, a terminal object `Unit`, a
-- distinguished code object `Code`, and a self-encoding `encode`.
--
-- WHY THIS EXISTS
--   EvalCorrectness / EvalFullCorrectness reason only about composition
--   and the encoding — never about `id`, the category laws, products, or
--   `μ`/`cata`. Parameterising them over a full CCT3Structure therefore
--   demanded more than they use. In particular a CCT3Structure carries a
--   HIGHER-ORDER `μ : (Obj → Obj) → Obj`, which a first-order
--   functor-code syntax (e.g. the bootstrap normalizer's `μ_ : Func → Ty`)
--   cannot supply — so it could not instantiate the theorems at all.
--
--   Stripping the parameterisation to exactly what is used is a strict
--   generalisation: it limits nothing (existing CCT3Structures still
--   qualify, via `fromCCT3` below) and ENABLES instantiation by any
--   self-encoding carrier, regardless of how it represents functors.
--
-- TOWER NOTE
--   The theorems do not USE μ, but a meaningful `Code = μ TermF` object
--   can only EXIST when the provider has μ. So "needs CCT3" is a fact
--   about whoever supplies Code/encode, not about the theorem statement.
--
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Theory.RanzowFixpoint.SelfEncoding where

------------------------------------------------------------------------
-- The minimal self-encoding carrier.
------------------------------------------------------------------------

record SelfEncoding : Set₁ where
  field
    Obj    : Set
    Hom    : Obj → Obj → Set
    _∘_    : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    Unit   : Obj
    Code   : Obj
    encode : ∀ {A B} → Hom A B → Hom Unit Code

  infixr 9 _∘_

------------------------------------------------------------------------
-- Adapter: every CCT3Structure equipped with an EncodingScheme yields a
-- SelfEncoding — so existing tower-based syntaxes instantiate the
-- evaluator theorems with a one-liner and lose nothing.
------------------------------------------------------------------------

open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.RanzowFixpoint using (EncodingScheme)

fromCCT3 : (S : CCT3Structure) → EncodingScheme S → SelfEncoding
fromCCT3 S E = record
  { Obj    = Obj
  ; Hom    = Hom
  ; _∘_    = _∘_
  ; Unit   = Unit
  ; Code   = EncodingScheme.Code E
  ; encode = EncodingScheme.encode E
  }
  where open CCT3Structure S
