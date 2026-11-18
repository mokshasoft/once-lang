{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Scope — what is in scope where a term is typed.
--
-- A typing context (`NamedCtx`) holds:
--   * the kinds of the type variables of the definition being typed (`kinds`):
--     a polymorphic definition's body is typed once, over its parameters;
--   * the local variables, twice: by name (`named`, innermost first) and as
--     the de Bruijn context the derivation is indexed by (`debruijn`), typed
--     over those type variables;
--   * the program's monomorphic definitions in scope (`imports`, ground);
--   * its polymorphic definitions, as a telescope (`polys`): each entry's
--     prefix holds only the definitions declared before it;
--   * its signature Σ, the declared external operations (`sig`, ground).
--
-- `headView` and `genKindView` read an application's head and a generator's
-- kind, which decide the rule an application takes.
------------------------------------------------------------------------

module Once.TypeCheck.Scope where

import Data.String
import Data.String.Properties as StrProp
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Grade using (Quantity; Many)
open import Once.Spec.Type using (Ty; Type; KCtx)
open import Once.Spec.Surface.Syntax using (PolyType)
import Once.Spec.Surface.Generators as G
open import Once.Spec.Surface.Syntax using (Expr)
import Once.Spec.Surface.Syntax as Raw
open import Once.Context using (SVar; svar)
open import Once.Spec.Context using (_▸_)
import Once.Context as Surface
import Once.Spec.Context as Surface

------------------------------------------------------------------------
-- Local variables, by name
------------------------------------------------------------------------

record Binding (m : ℕ) : Set where
  constructor mkBinding
  field
    name     : String
    type     : Ty m
    quantity : Quantity

open Binding

-- The most recent binding first.
Ctx : ℕ → Set
Ctx m = List (Binding m)

-- Extend with a binding of unrestricted usage.
extendCtx : ∀ {m} → Ctx m → String → Ty m → Ctx m
extendCtx Γ x A = mkBinding x A Many ∷ Γ

------------------------------------------------------------------------
-- Definitions in scope
------------------------------------------------------------------------

-- Monomorphic definitions, and the signature's operations, by name.
Imports : Set
Imports = List (String × Type)

-- Polymorphic definitions: name, schema and body, most recent first.
PolyCtx : Set
PolyCtx = List (String × PolyType × Expr)

lookupImport : Imports → String → Maybe Type
lookupImport [] _ = nothing
lookupImport ((n , ty) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just ty
... | no  _ = lookupImport rest x

-- A polymorphic definition and its prefix: the definitions its body may
-- refer to.
lookupPolyPrefix : PolyCtx → String → Maybe (PolyType × Expr × PolyCtx)
lookupPolyPrefix [] _ = nothing
lookupPolyPrefix ((n , s , b) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just (s , b , rest)
... | no  _ = lookupPolyPrefix rest x

------------------------------------------------------------------------
-- The typing context
------------------------------------------------------------------------

record NamedCtx (m : ℕ) : Set where
  constructor mkCtx
  field
    size        : ℕ
    named       : Ctx m
    debruijn    : Surface.Ctx m size
    imports     : Imports
    polys       : PolyCtx
    sig         : Imports
    kinds       : KCtx m

extendNamedCtx : ∀ {m} → NamedCtx m → String → Ty m → NamedCtx m
extendNamedCtx ctx x A =
  mkCtx (suc (NamedCtx.size ctx)) (extendCtx (NamedCtx.named ctx) x A) (NamedCtx.debruijn ctx ▸ A)
        (NamedCtx.imports ctx) (NamedCtx.polys ctx) (NamedCtx.sig ctx) (NamedCtx.kinds ctx)

-- A local variable: the innermost binding of the name, as a de Bruijn
-- variable of the context.
-- (Top-level steps, not `with`: a proof follows the lookup by the decision
-- and the inner result it is given.)
lookupLocal-go : ∀ {k m} (x : String) (Γ : Ctx k) (Δ' : Surface.Ctx k m)
               → Maybe (∃[ A ] ∃[ Ψ ] (SVar Δ' Ψ A))
-- the outer binder, past an inner result
lookupLocal-next : ∀ {k m} {Δ' : Surface.Ctx k m} {B} → Maybe (∃[ A ] ∃[ Ψ ] (SVar Δ' Ψ A))
                 → Maybe (∃[ A ] ∃[ Ψ ] (SVar (Δ' ▸ B) Ψ A))
lookupLocal-next nothing                 = nothing
lookupLocal-next (just (A , Ψ , svar i)) = just (_ , _ , svar (suc i))

-- the innermost binder: the name's, or the lookup goes on
lookupLocal-at : ∀ {k m} (x : String) (b : Binding k) (Γ' : Ctx k) (Δ' : Surface.Ctx k m) {B}
               → Dec (x ≡ name b) → Maybe (∃[ A ] ∃[ Ψ ] (SVar (Δ' ▸ B) Ψ A))
lookupLocal-at x b Γ' Δ' (yes _) = just (_ , _ , svar zero)
lookupLocal-at x b Γ' Δ' (no _)  = lookupLocal-next (lookupLocal-go x Γ' Δ')

lookupLocal-go x [] Surface.∅ = nothing
lookupLocal-go x [] (_ ▸ _) = nothing
lookupLocal-go x (_ ∷ _) Surface.∅ = nothing
lookupLocal-go x (b ∷ Γ') (Δ' ▸ B) = lookupLocal-at x b Γ' Δ' (Data.String._≟_ x (name b))

lookupLocal : ∀ {m} (ctx : NamedCtx m) → String
            → Maybe (∃[ A ] ∃[ Ψ ] (SVar (NamedCtx.debruijn ctx) Ψ A))
lookupLocal ctx x = lookupLocal-go x (NamedCtx.named ctx) (NamedCtx.debruijn ctx)

------------------------------------------------------------------------
-- Application heads and generator kinds (plan 0.151)
------------------------------------------------------------------------

-- The head of an application, by form: a generator, a generator given one
-- argument or two, a λ, or anything else. With the generator's kind
-- (`GenKindView`) it decides the rule an application takes
-- (`Spec.Surface.Typing`: `CheckHead`, `PartialCombinator`, `OwnCheck`).
-- Not indexed by the expression, so reading it leaves the expression as it
-- is (`head-is` recovers the form).
data Head : Set where
  hv-gen   : G.Gen → Head
  hv-gen₁  : G.Gen → Expr → Head
  hv-gen₂  : G.Gen → Expr → Expr → Head
  hv-lam   : Head
  hv-other : Head

headView : Expr → Head
headView (Raw.RGen g)                           = hv-gen g
headView (Raw.RApp (Raw.RGen g) a)              = hv-gen₁ g a
headView (Raw.RApp (Raw.RApp (Raw.RGen g) a) b) = hv-gen₂ g a b
headView (Raw.RLam x b)                         = hv-lam
{-# CATCHALL #-}
headView _                                      = hv-other

-- A generator's kind, as the classes the rules read.
data GenKindView (g : G.Gen) : Set where
  gk-map   : G.IsMap (G.kind g) → GenKindView g
  gk-const : G.IsConstant (G.kind g) → GenKindView g
  gk-comb₁ : G.IsCombinator 1 (G.kind g) → GenKindView g
  gk-comb₂ : G.IsCombinator 2 (G.kind g) → GenKindView g

genKindView : (g : G.Gen) → GenKindView g
genKindView G.id       = gk-map G.is-map
genKindView G.compose  = gk-comb₂ G.is-combinator
genKindView G.fst      = gk-map G.is-map
genKindView G.snd      = gk-map G.is-map
genKindView G.terminal = gk-map G.is-map
genKindView G.pair     = gk-comb₂ G.is-combinator
genKindView G.inl      = gk-map G.is-map
genKindView G.inr      = gk-map G.is-map
genKindView G.initial  = gk-map G.is-map
genKindView G.case     = gk-comb₂ G.is-combinator
genKindView G.apply    = gk-map G.is-map
genKindView G.curry    = gk-comb₁ G.is-combinator
genKindView G.In       = gk-map G.is-map
genKindView G.cata     = gk-comb₁ G.is-combinator
genKindView G.Out      = gk-map G.is-map
genKindView G.ana      = gk-comb₁ G.is-combinator
genKindView G.unit     = gk-const G.is-constant
genKindView G.toFloat  = gk-const G.is-constant
