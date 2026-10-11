{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Typing.Scope — what is in scope where a term is typed.
--
-- A typing context (`NamedCtx`) holds:
--   * the local variables, twice: by name (`named`, innermost first) and as
--     the de Bruijn context the derivation is indexed by (`debruijn`);
--   * the program's monomorphic definitions in scope (`imports`);
--   * its polymorphic definitions, as a telescope (`polys`): each entry's
--     prefix holds only the definitions declared before it;
--   * its signature Σ, the declared external operations (`sig`).
--
-- `classifyAppHead` recognises the applied generators that have typing rules
-- of their own; the general application rule applies to every other head.
------------------------------------------------------------------------

module Once.Spec.Typing.Scope where

import Data.String
import Data.String.Properties as StrProp
open import Agda.Builtin.Equality.Erase using (primEraseEquality)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; _≟_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Once.Spec.Type.Grade using (Quantity; Many)
open import Once.Spec.Type using (Type)
open import Once.Spec.Type.Poly using (PolyType)
open import Once.Spec.Name using (canonical; gen; generatorNS)
open import Once.Spec.Syntax using (RawExpr)
import Once.Spec.Syntax as Raw
open import Once.Spec.Context using (_,_^_; SVar; svar)
import Once.Spec.Context as Surface

------------------------------------------------------------------------
-- Local variables, by name
------------------------------------------------------------------------

record Binding : Set where
  constructor mkBinding
  field
    name     : String
    type     : Type
    quantity : Quantity

open Binding

-- The most recent binding first.
Ctx : Set
Ctx = List Binding

-- Extend with a binding of unrestricted usage.
extendCtx : Ctx → String → Type → Ctx
extendCtx Γ x A = mkBinding x A Many ∷ Γ

------------------------------------------------------------------------
-- Definitions in scope
------------------------------------------------------------------------

-- Monomorphic definitions, and the signature's operations, by name.
Imports : Set
Imports = List (String × Type)

-- Polymorphic definitions: name, schema and body, most recent first.
PolyCtx : Set
PolyCtx = List (String × PolyType × RawExpr)

lookupImport : Imports → String → Maybe Type
lookupImport [] _ = nothing
lookupImport ((n , ty) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just ty
... | no  _ = lookupImport rest x

-- A polymorphic definition and its prefix: the definitions its body may
-- refer to.
lookupPolyPrefix : PolyCtx → String → Maybe (PolyType × RawExpr × PolyCtx)
lookupPolyPrefix [] _ = nothing
lookupPolyPrefix ((n , s , b) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just (s , b , rest)
... | no  _ = lookupPolyPrefix rest x

------------------------------------------------------------------------
-- The typing context
------------------------------------------------------------------------

record NamedCtx : Set where
  constructor mkCtx
  field
    size        : ℕ
    named       : Ctx
    debruijn    : Surface.Ctx size
    imports     : Imports
    polys       : PolyCtx
    sig         : Imports

extendNamedCtx : NamedCtx → String → Type → NamedCtx
extendNamedCtx (mkCtx n Γ Δ imps polys sg) x A =
  mkCtx (suc n) (extendCtx Γ x A) (Δ , A ^ Many) imps polys sg

-- A local variable: the innermost binding of the name, as a de Bruijn
-- variable of the context.
lookupLocal-go : ∀ {m} (x : String) (Γ : Ctx) (Δ' : Surface.Ctx m)
               → Maybe (∃[ A ] ∃[ Ψ ] (SVar Δ' Ψ A))
lookupLocal-go x [] Surface.∅ = nothing
lookupLocal-go x [] (_ , _ ^ _) = nothing
lookupLocal-go x (_ ∷ _) Surface.∅ = nothing
lookupLocal-go {m = suc m'} x (b ∷ Γ') (Δ' , B ^ _) with Data.String._≟_ x (name b)
... | yes _ = just (_ , _ , svar zero)
... | no _  with lookupLocal-go x Γ' Δ'
...   | nothing = nothing
...   | just (A , Ψ , svar i) = just (_ , _ , svar (suc i))

lookupLocal : (ctx : NamedCtx) → String
            → Maybe (∃[ A ] ∃[ Ψ ] (SVar (NamedCtx.debruijn ctx) Ψ A))
lookupLocal ctx x = lookupLocal-go x (NamedCtx.named ctx) (NamedCtx.debruijn ctx)

------------------------------------------------------------------------
-- Generator heads
------------------------------------------------------------------------

-- String equality whose `yes` proof is erased, so a classified head reduces
-- as soon as the strings are equal.
infix 4 _≟ₛ_
_≟ₛ_ : DecidableEquality String
x ≟ₛ y = map′ primEraseEquality (λ p → p) (x ≟ y)

-- The applied generators with typing rules of their own.
data PolyBuiltinApp : Set where
  pba-id pba-fst pba-snd pba-terminal : PolyBuiltinApp  -- infer-mode successes
  pba-inl pba-inr pba-initial : PolyBuiltinApp          -- infer-mode rejections
  pba-pair-applied : PolyBuiltinApp                     -- `RApp (RVar "pair") _` head, check mode
  pba-compose-applied : PolyBuiltinApp                  -- `RApp (RVar "compose") _` head, check mode
  pba-case-applied : PolyBuiltinApp                     -- `RApp (RVar "case") _` head, check mode (copair)
  pba-curry : PolyBuiltinApp                            -- 1-arg `curry f`, check mode
  pba-apply : PolyBuiltinApp                            -- 1-arg `apply p`, infer / check mode
  pba-In : PolyBuiltinApp                               -- 1-arg `In arg`, check mode (μ intro)
  pba-cata : PolyBuiltinApp                             -- 1-arg `cata alg`, check mode (fold)
  pba-ana  : PolyBuiltinApp                             -- 1-arg `ana coalg`, check mode (unfold)
  pba-Out  : PolyBuiltinApp                             -- 1-arg `Out v`, INFER mode (force)

data AppHeadView : RawExpr → Set where
  ahv-id       : AppHeadView (Raw.RResolved (gen "id"))
  ahv-fst      : AppHeadView (Raw.RResolved (gen "fst"))
  ahv-snd      : AppHeadView (Raw.RResolved (gen "snd"))
  ahv-terminal : AppHeadView (Raw.RResolved (gen "terminal"))
  ahv-inl      : AppHeadView (Raw.RResolved (gen "inl"))
  ahv-inr      : AppHeadView (Raw.RResolved (gen "inr"))
  ahv-initial  : AppHeadView (Raw.RResolved (gen "initial"))
  ahv-curry    : AppHeadView (Raw.RResolved (gen "curry"))
  ahv-apply    : AppHeadView (Raw.RResolved (gen "apply"))
  ahv-In       : AppHeadView (Raw.RResolved (gen "In"))
  ahv-cata     : AppHeadView (Raw.RResolved (gen "cata"))
  ahv-ana      : AppHeadView (Raw.RResolved (gen "ana"))
  ahv-Out      : AppHeadView (Raw.RResolved (gen "Out"))
  ahv-pair-applied    : ∀ {f'} → AppHeadView (Raw.RApp (Raw.RResolved (gen "pair")) f')
  ahv-compose-applied : ∀ {f'} → AppHeadView (Raw.RApp (Raw.RResolved (gen "compose")) f')
  ahv-case-applied    : ∀ {f'} → AppHeadView (Raw.RApp (Raw.RResolved (gen "case")) f')
  ahv-other    : ∀ {f} → AppHeadView f

classifyAppHeadView : (f : RawExpr) → AppHeadView f
classifyAppHeadView (Raw.RResolved (canonical (ns ∷ g ∷ []))) with ns ≟ₛ generatorNS
... | no _ = ahv-other
... | yes refl with g ≟ₛ "id"
...   | yes refl = ahv-id
...   | no  _ with g ≟ₛ "fst"
...     | yes refl = ahv-fst
...     | no  _ with g ≟ₛ "snd"
...       | yes refl = ahv-snd
...       | no  _ with g ≟ₛ "terminal"
...         | yes refl = ahv-terminal
...         | no  _ with g ≟ₛ "inl"
...           | yes refl = ahv-inl
...           | no  _ with g ≟ₛ "inr"
...             | yes refl = ahv-inr
...             | no  _ with g ≟ₛ "initial"
...               | yes refl = ahv-initial
...               | no  _ with g ≟ₛ "curry"
...                 | yes refl = ahv-curry
...                 | no  _ with g ≟ₛ "apply"
...                   | yes refl = ahv-apply
...                   | no  _ with g ≟ₛ "In"
...                     | yes refl = ahv-In
...                     | no  _ with g ≟ₛ "cata"
...                       | yes refl = ahv-cata
...                       | no  _ with g ≟ₛ "ana"
...                         | yes refl = ahv-ana
...                         | no  _ with g ≟ₛ "Out"
...                           | yes refl = ahv-Out
...                           | no  _ = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RResolved (canonical (ns ∷ g ∷ []))) _) with ns ≟ₛ generatorNS
... | no _ = ahv-other
... | yes refl with g ≟ₛ "pair"
...   | yes refl = ahv-pair-applied
...   | no  _ with g ≟ₛ "compose"
...     | yes refl = ahv-compose-applied
...     | no  _ with g ≟ₛ "case"
...       | yes refl = ahv-case-applied
...       | no  _ = ahv-other
classifyAppHeadView (Raw.RResolved (canonical []))            = ahv-other
classifyAppHeadView (Raw.RResolved (canonical (_ ∷ [])))      = ahv-other
classifyAppHeadView (Raw.RResolved (canonical (_ ∷ _ ∷ _ ∷ _))) = ahv-other
classifyAppHeadView (Raw.RVar _)                        = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RResolved (canonical [])) _)       = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RResolved (canonical (_ ∷ []))) _) = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RResolved (canonical (_ ∷ _ ∷ _ ∷ _))) _) = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RVar _) _)           = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RApp _ _) _)         = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RQualified _ _) _)   = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RLam _ _) _)         = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RLet _ _ _) _)       = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RPair _ _) _)        = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) = ahv-other
classifyAppHeadView (Raw.RApp Raw.RUnit _)              = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RInt _) _)           = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RFloat _ _ _ _) _)     = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RStringLit _) _)     = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RAnnot _ _) _)       = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RBinOp _ _ _) _)     = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RUnaryOp _ _) _)     = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RAna _ _) _)         = ahv-other
classifyAppHeadView (Raw.RAna _ _)            = ahv-other
classifyAppHeadView (Raw.RQualified _ _)      = ahv-other
classifyAppHeadView (Raw.RLam _ _)            = ahv-other
classifyAppHeadView (Raw.RLet _ _ _)          = ahv-other
classifyAppHeadView (Raw.RPair _ _)           = ahv-other
classifyAppHeadView (Raw.RDestruct _ _ _ _ _) = ahv-other
classifyAppHeadView Raw.RUnit                 = ahv-other
classifyAppHeadView (Raw.RInt _)              = ahv-other
classifyAppHeadView (Raw.RFloat _ _ _ _)        = ahv-other
classifyAppHeadView (Raw.RStringLit _)        = ahv-other
classifyAppHeadView (Raw.RAnnot _ _)          = ahv-other
classifyAppHeadView (Raw.RBinOp _ _ _)        = ahv-other
classifyAppHeadView (Raw.RUnaryOp _ _)        = ahv-other

viewToPba : ∀ {f} → AppHeadView f → Maybe PolyBuiltinApp
viewToPba ahv-id              = just pba-id
viewToPba ahv-fst             = just pba-fst
viewToPba ahv-snd             = just pba-snd
viewToPba ahv-terminal        = just pba-terminal
viewToPba ahv-inl             = just pba-inl
viewToPba ahv-inr             = just pba-inr
viewToPba ahv-initial         = just pba-initial
viewToPba ahv-curry           = just pba-curry
viewToPba ahv-apply           = just pba-apply
viewToPba ahv-In              = just pba-In
viewToPba ahv-cata            = just pba-cata
viewToPba ahv-ana             = just pba-ana
viewToPba ahv-Out             = just pba-Out
viewToPba ahv-pair-applied    = just pba-pair-applied
viewToPba ahv-compose-applied = just pba-compose-applied
viewToPba ahv-case-applied    = just pba-case-applied
viewToPba ahv-other           = nothing

classifyAppHead : RawExpr → Maybe PolyBuiltinApp
classifyAppHead f = viewToPba (classifyAppHeadView f)
