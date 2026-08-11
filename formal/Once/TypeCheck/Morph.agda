-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Morph
--
-- A self-contained *syntactic* compiler from point-free morphism
-- expressions (`MorphRaw`) to closed CCC morphisms (`IR X A`). This is
-- what `cata`'s algebra slot needs: `IR.Cata` requires a closed arrow
-- `IR (⟦F⟧T A) A`, and a closed point-free algebra (built from the CCC
-- morphism builtins — `id/fst/snd/inl/inr/terminal/initial/case`, plus
-- nested recursion schemes) compiles directly to one.
--
-- Living BELOW both `Judgment` and `Elaborate` (it depends only on
-- `Raw`, `Type`, `IR`), it lets the `cata` typing rule carry decidable
-- equation premises (`morphRaw? alg ≡ just mr`, `morphToIR mr … ≡ just
-- algIR`) rather than a property of the elaborated term — which keeps
-- `check-complete` total + postulate-free without any bidirectional
-- coherence with the main elaborator (the IR comes from `morphToIR`,
-- not from extracting the elaboration).
------------------------------------------------------------------------

module Once.TypeCheck.Morph where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
import Data.String.Properties as StrProp
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer;
                             _*_; _+_; _⇒[_]_; μ-type; ν-type;
                             Functor; K; Id; _⊕_; _⊗_)
open import Once.IR as IR using (IR; Heap)
open import Once.IRTy using (⌊_⌋)
open import Once.TypeCheck.Raw as Raw using (RawExpr; RVar; RApp)

------------------------------------------------------------------------
-- Lightweight Maybe-valued type equality (positive cases only — a
-- `nothing` is "not equal", which is all `morphToIR` needs).
------------------------------------------------------------------------

_≡T?_ : (A B : Type) → Maybe (A ≡ B)
Unit   ≡T? Unit   = just refl
Void   ≡T? Void   = just refl
Int    ≡T? Int    = just refl
Float  ≡T? Float  = just refl
Str    ≡T? Str    = just refl
Buffer ≡T? Buffer = just refl
(A₁ * B₁) ≡T? (A₂ * B₂) with A₁ ≡T? A₂ | B₁ ≡T? B₂
... | just refl | just refl = just refl
... | _         | _         = nothing
(A₁ + B₁) ≡T? (A₂ + B₂) with A₁ ≡T? A₂ | B₁ ≡T? B₂
... | just refl | just refl = just refl
... | _         | _         = nothing
_ ≡T? _ = nothing

------------------------------------------------------------------------
-- The closed point-free morphism forms.
------------------------------------------------------------------------

data MorphRaw : RawExpr → Set where
  mr-id       : MorphRaw (RVar "id")
  mr-fst      : MorphRaw (RVar "fst")
  mr-snd      : MorphRaw (RVar "snd")
  mr-inl      : MorphRaw (RVar "inl")
  mr-inr      : MorphRaw (RVar "inr")
  mr-terminal : MorphRaw (RVar "terminal")
  mr-initial  : MorphRaw (RVar "initial")
  mr-case     : ∀ {f g} → MorphRaw f → MorphRaw g
              → MorphRaw (RApp (RApp (RVar "case") f) g)

------------------------------------------------------------------------
-- Decide whether a RawExpr is a point-free morphism form.
------------------------------------------------------------------------

morphRaw? : (e : RawExpr) → Maybe (MorphRaw e)
morphRaw? (RVar x) with StrProp._≟_ x "id"
... | yes refl = just mr-id
... | no _ with StrProp._≟_ x "fst"
...   | yes refl = just mr-fst
...   | no _ with StrProp._≟_ x "snd"
...     | yes refl = just mr-snd
...     | no _ with StrProp._≟_ x "inl"
...       | yes refl = just mr-inl
...       | no _ with StrProp._≟_ x "inr"
...         | yes refl = just mr-inr
...         | no _ with StrProp._≟_ x "terminal"
...           | yes refl = just mr-terminal
...           | no _ with StrProp._≟_ x "initial"
...             | yes refl = just mr-initial
...             | no _ = nothing
morphRaw? (RApp (RApp (RVar x) f) g) with StrProp._≟_ x "case"
... | yes refl with morphRaw? f | morphRaw? g
...   | just mf | just mg = just (mr-case mf mg)
...   | _       | _       = nothing
morphRaw? (RApp (RApp (RVar x) f) g) | no _ = nothing
morphRaw? _ = nothing

------------------------------------------------------------------------
-- Compile a morphism form to a closed `IR X A` at the demanded source
-- (`X`) and target (`A`) types. `nothing` when the form doesn't fit
-- those types (e.g. `inl` whose target isn't a sum starting at X).
------------------------------------------------------------------------

morphToIR : ∀ {alg} → MorphRaw alg → (X A : Type) → Maybe (IR ⌊ X ⌋ ⌊ A ⌋)
morphToIR mr-id X A with X ≡T? A
... | just refl = just IR.id
... | nothing   = nothing
morphToIR mr-fst (P * Q) A with P ≡T? A
... | just refl = just IR.fst
... | nothing   = nothing
morphToIR mr-fst _ _ = nothing
morphToIR mr-snd (P * Q) A with Q ≡T? A
... | just refl = just IR.snd
... | nothing   = nothing
morphToIR mr-snd _ _ = nothing
morphToIR mr-inl X (L + R) with X ≡T? L
... | just refl = just (IR.inl {A = ⌊ X ⌋} {B = ⌊ R ⌋} Heap)
... | nothing   = nothing
morphToIR mr-inl _ _ = nothing
morphToIR mr-inr X (L + R) with X ≡T? R
... | just refl = just (IR.inr {A = ⌊ L ⌋} {B = ⌊ X ⌋} Heap)
... | nothing   = nothing
morphToIR mr-inr _ _ = nothing
morphToIR mr-terminal X Unit = just IR.terminal
morphToIR mr-terminal _ _ = nothing
morphToIR mr-initial Void A = just IR.initial
morphToIR mr-initial _ _ = nothing
morphToIR (mr-case mf mg) (P + Q) A with morphToIR mf P A | morphToIR mg Q A
... | just cf | just cg = just (IR.case cf cg)
... | _       | _       = nothing
morphToIR (mr-case mf mg) _ _ = nothing
