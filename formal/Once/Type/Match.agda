-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Match — the DECIDER for schema instances (implementation, not
-- the type language): template matching of a `PolyType` against a `Type`.
-- Moved out of `Once.Type` (plan 0.103 phase 2a) so that it can decide
-- equality with `_≟T_`; `Once.Type.Instance` proves it sound and complete
-- for `IsInstance`.
------------------------------------------------------------------------

module Once.Type.Match where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
import Data.String as Str
open import Relation.Nullary using (Dec; yes; no)

open import Once.Type
open import Once.Type.DecEq using (_≟T_)

-- Plan 0.6.2 Phase 1 (load-bearing POC for Option C of D044's
-- follow-up). Given a PolyType schema with `PTVar` type variables
-- and a candidate ground Type, produces a TVar → Type substitution
-- that makes the schema match the ground type, or `nothing` if the
-- shapes don't line up or a TVar is bound to two distinct types.
--
-- D007-compatible: structural template matching, not unification.
-- No meta-variables. Total function.

Subst : Set
Subst = List (String × Type)

lookupSubst : String → Subst → Maybe Type
lookupSubst _ [] = nothing
lookupSubst x ((y , t) ∷ rest) with x Str.≟ y
... | yes _ = just t
... | no _  = lookupSubst x rest

-- Plan 0.103 phase 2a: decisions are `Dec`s, so the matcher's soundness is a
-- proof about the decided equalities rather than about a `Bool` comparison.
decide : ∀ {P : Set} {A : Set} → Dec P → Maybe A → Maybe A
decide (yes _) m = m
decide (no _)  _ = nothing

-- | Extend substitution with `(x, t)`; returns `nothing` if `x` was
-- already bound to a different type.
extendSubst-aux : String → Type → Subst → Maybe Type → Maybe Subst
extendSubst-aux x t s (just t′) = decide (t ≟T t′) (just s)
extendSubst-aux x t s nothing   = just ((x , t) ∷ s)

extendSubst : String → Type → Subst → Maybe Subst
extendSubst x t s = extendSubst-aux x t s (lookupSubst x s)

-- Maybe-handling helpers (no-with form).

maybe-bind : ∀ {A B : Set} → (A → Maybe B) → Maybe A → Maybe B
maybe-bind _ nothing  = nothing
maybe-bind f (just a) = f a

maybe-pair : ∀ {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
maybe-pair f (just a) (just b) = just (f a b)
maybe-pair _ (just _) nothing  = nothing
maybe-pair _ nothing  (just _) = nothing
maybe-pair _ nothing  nothing  = nothing

if-true-maybe : ∀ {A : Set} → Bool → Maybe A → Maybe A
if-true-maybe true  m = m
if-true-maybe false _ = nothing

-- | Instantiate a `PolyType` schema against a candidate ground `Type`.
-- The top-level wrapper runs the accumulator form with an empty
-- initial substitution.
mutual
  instantiate : PolyType → Type → Maybe Subst
  instantiate p t = instantiateAcc p t []

  instantiateAcc : PolyType → Type → Subst → Maybe Subst
  instantiateAcc (PTVar x)       t               s = extendSubst x t s
  instantiateAcc PUnit           Unit            s = just s
  instantiateAcc PVoid           Void            s = just s
  instantiateAcc PInt            Int             s = just s
  instantiateAcc PFloat          Float           s = just s
  instantiateAcc PStr            Str             s = just s
  instantiateAcc PBuffer         Buffer          s = just s
  instantiateAcc (A P* B)        (a * b)         s =
    maybe-bind (instantiateAcc B b) (instantiateAcc A a s)
  instantiateAcc (A P+ B)        (a + b)         s =
    maybe-bind (instantiateAcc B b) (instantiateAcc A a s)
  instantiateAcc (A P⇒[ q ] B)   (a ⇒[ mk-kind q' pure ] b)   s =
    decide (q ≟q q')
      (maybe-bind (instantiateAcc B b) (instantiateAcc A a s))
  -- `Eff A B` is exactly the `Many` effectful arrow (plan 0.103 phase 2a:
  -- the decider agrees with `substPoly`).
  instantiateAcc (PEff A B)      (a ⇒[ mk-kind Many eff ] b)  s =
    maybe-bind (instantiateAcc B b) (instantiateAcc A a s)
  instantiateAcc (PEff _ _)      (_ ⇒[ mk-kind Zero eff ] _)  _ = nothing
  instantiateAcc (PEff _ _)      (_ ⇒[ mk-kind One eff ] _)   _ = nothing
  instantiateAcc (Pμ-type F)     (μ-type f)      s = instantiateFunctor F f s
  instantiateAcc (Pν-type F pure) (ν-type f pure) s = instantiateFunctor F f s
  instantiateAcc (Pν-type F eff)  (ν-type f eff)  s = instantiateFunctor F f s
  instantiateAcc (Pν-type _ pure) (ν-type _ eff)  _ = nothing
  instantiateAcc (Pν-type _ eff)  (ν-type _ pure) _ = nothing
  -- Shape mismatch on each PolyType constructor (no catch-all).
  instantiateAcc PUnit           Void            _ = nothing
  instantiateAcc PUnit           (_ * _)         _ = nothing
  instantiateAcc PUnit           (_ + _)         _ = nothing
  instantiateAcc PUnit           (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PUnit           (μ-type _)      _ = nothing
  instantiateAcc PUnit           (ν-type _ _)      _ = nothing
  instantiateAcc PUnit           Int             _ = nothing
  instantiateAcc PUnit           Float           _ = nothing
  instantiateAcc PUnit           Str             _ = nothing
  instantiateAcc PUnit           Buffer          _ = nothing
  instantiateAcc PVoid           Unit            _ = nothing
  instantiateAcc PVoid           (_ * _)         _ = nothing
  instantiateAcc PVoid           (_ + _)         _ = nothing
  instantiateAcc PVoid           (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PVoid           (μ-type _)      _ = nothing
  instantiateAcc PVoid           (ν-type _ _)      _ = nothing
  instantiateAcc PVoid           Int             _ = nothing
  instantiateAcc PVoid           Float           _ = nothing
  instantiateAcc PVoid           Str             _ = nothing
  instantiateAcc PVoid           Buffer          _ = nothing
  instantiateAcc (_ P* _)        Unit            _ = nothing
  instantiateAcc (_ P* _)        Void            _ = nothing
  instantiateAcc (_ P* _)        (_ + _)         _ = nothing
  instantiateAcc (_ P* _)        (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc (_ P* _)        (μ-type _)      _ = nothing
  instantiateAcc (_ P* _)        (ν-type _ _)      _ = nothing
  instantiateAcc (_ P* _)        Int             _ = nothing
  instantiateAcc (_ P* _)        Float           _ = nothing
  instantiateAcc (_ P* _)        Str             _ = nothing
  instantiateAcc (_ P* _)        Buffer          _ = nothing
  instantiateAcc (_ P+ _)        Unit            _ = nothing
  instantiateAcc (_ P+ _)        Void            _ = nothing
  instantiateAcc (_ P+ _)        (_ * _)         _ = nothing
  instantiateAcc (_ P+ _)        (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc (_ P+ _)        (μ-type _)      _ = nothing
  instantiateAcc (_ P+ _)        (ν-type _ _)      _ = nothing
  instantiateAcc (_ P+ _)        Int             _ = nothing
  instantiateAcc (_ P+ _)        Float           _ = nothing
  instantiateAcc (_ P+ _)        Str             _ = nothing
  instantiateAcc (_ P+ _)        Buffer          _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Unit            _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Void            _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (_ * _)         _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (_ + _)         _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (_ ⇒[ mk-kind _ eff ] _) _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (μ-type _)      _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (ν-type _ _)      _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Int             _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Float           _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Str             _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Buffer          _ = nothing
  instantiateAcc (PEff _ _)      Unit            _ = nothing
  instantiateAcc (PEff _ _)      Void            _ = nothing
  instantiateAcc (PEff _ _)      (_ * _)         _ = nothing
  instantiateAcc (PEff _ _)      (_ + _)         _ = nothing
  instantiateAcc (PEff _ _)      (_ ⇒[ mk-kind _ pure ] _) _ = nothing
  instantiateAcc (PEff _ _)      (μ-type _)      _ = nothing
  instantiateAcc (PEff _ _)      (ν-type _ _)      _ = nothing
  instantiateAcc (PEff _ _)      Int             _ = nothing
  instantiateAcc (PEff _ _)      Float           _ = nothing
  instantiateAcc (PEff _ _)      Str             _ = nothing
  instantiateAcc (PEff _ _)      Buffer          _ = nothing
  instantiateAcc (Pμ-type _)     Unit            _ = nothing
  instantiateAcc (Pμ-type _)     Void            _ = nothing
  instantiateAcc (Pμ-type _)     (_ * _)         _ = nothing
  instantiateAcc (Pμ-type _)     (_ + _)         _ = nothing
  instantiateAcc (Pμ-type _)     (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc (Pμ-type _)     (ν-type _ _)      _ = nothing
  instantiateAcc (Pμ-type _)     Int             _ = nothing
  instantiateAcc (Pμ-type _)     Float           _ = nothing
  instantiateAcc (Pμ-type _)     Str             _ = nothing
  instantiateAcc (Pμ-type _)     Buffer          _ = nothing
  instantiateAcc (Pν-type _ _)     Unit            _ = nothing
  instantiateAcc (Pν-type _ _)     Void            _ = nothing
  instantiateAcc (Pν-type _ _)     (_ * _)         _ = nothing
  instantiateAcc (Pν-type _ _)     (_ + _)         _ = nothing
  instantiateAcc (Pν-type _ _)     (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc (Pν-type _ _)     (μ-type _)      _ = nothing
  instantiateAcc (Pν-type _ _)     Int             _ = nothing
  instantiateAcc (Pν-type _ _)     Float           _ = nothing
  instantiateAcc (Pν-type _ _)     Str             _ = nothing
  instantiateAcc (Pν-type _ _)     Buffer          _ = nothing
  instantiateAcc PInt            Unit            _ = nothing
  instantiateAcc PInt            Void            _ = nothing
  instantiateAcc PInt            (_ * _)         _ = nothing
  instantiateAcc PInt            (_ + _)         _ = nothing
  instantiateAcc PInt            (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PInt            (μ-type _)      _ = nothing
  instantiateAcc PInt            (ν-type _ _)      _ = nothing
  instantiateAcc PInt            Float           _ = nothing
  instantiateAcc PInt            Str             _ = nothing
  instantiateAcc PInt            Buffer          _ = nothing
  instantiateAcc PFloat          Unit            _ = nothing
  instantiateAcc PFloat          Void            _ = nothing
  instantiateAcc PFloat          (_ * _)         _ = nothing
  instantiateAcc PFloat          (_ + _)         _ = nothing
  instantiateAcc PFloat          (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PFloat          (μ-type _)      _ = nothing
  instantiateAcc PFloat          (ν-type _ _)      _ = nothing
  instantiateAcc PFloat          Int             _ = nothing
  instantiateAcc PFloat          Str             _ = nothing
  instantiateAcc PFloat          Buffer          _ = nothing
  instantiateAcc PStr            Unit            _ = nothing
  instantiateAcc PStr            Void            _ = nothing
  instantiateAcc PStr            (_ * _)         _ = nothing
  instantiateAcc PStr            (_ + _)         _ = nothing
  instantiateAcc PStr            (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PStr            (μ-type _)      _ = nothing
  instantiateAcc PStr            (ν-type _ _)      _ = nothing
  instantiateAcc PStr            Int             _ = nothing
  instantiateAcc PStr            Float           _ = nothing
  instantiateAcc PStr            Buffer          _ = nothing
  instantiateAcc PBuffer         Unit            _ = nothing
  instantiateAcc PBuffer         Void            _ = nothing
  instantiateAcc PBuffer         (_ * _)         _ = nothing
  instantiateAcc PBuffer         (_ + _)         _ = nothing
  instantiateAcc PBuffer         (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PBuffer         (μ-type _)      _ = nothing
  instantiateAcc PBuffer         (ν-type _ _)      _ = nothing
  instantiateAcc PBuffer         Int             _ = nothing
  instantiateAcc PBuffer         Float           _ = nothing
  instantiateAcc PBuffer         Str             _ = nothing

  instantiateFunctor : PolyFunctor → Functor → Subst → Maybe Subst
  instantiateFunctor (PK A)    (K a)   s = instantiateAcc A a s
  instantiateFunctor PId       Id      s = just s
  instantiateFunctor (F P⊕ G) (f ⊕ g) s =
    maybe-bind (instantiateFunctor G g) (instantiateFunctor F f s)
  instantiateFunctor (F P⊗ G) (f ⊗ g) s =
    maybe-bind (instantiateFunctor G g) (instantiateFunctor F f s)
  instantiateFunctor (PK _)    Id      _ = nothing
  instantiateFunctor (PK _)    (_ ⊕ _) _ = nothing
  instantiateFunctor (PK _)    (_ ⊗ _) _ = nothing
  instantiateFunctor PId       (K _)   _ = nothing
  instantiateFunctor PId       (_ ⊕ _) _ = nothing
  instantiateFunctor PId       (_ ⊗ _) _ = nothing
  instantiateFunctor (_ P⊕ _)  (K _)   _ = nothing
  instantiateFunctor (_ P⊕ _)  Id      _ = nothing
  instantiateFunctor (_ P⊕ _)  (_ ⊗ _) _ = nothing
  instantiateFunctor (_ P⊗ _)  (K _)   _ = nothing
  instantiateFunctor (_ P⊗ _)  Id      _ = nothing
  instantiateFunctor (_ P⊗ _)  (_ ⊕ _) _ = nothing

-- | Apply a substitution to a PolyType, producing a ground Type.
-- Returns `nothing` if the PolyType contains a `PTVar` not covered
-- by the substitution (shouldn't happen after a successful
-- `instantiate`, but we return Maybe for safety rather than assuming).
mutual
  applySubst : Subst → PolyType → Maybe Type
  applySubst s (PTVar x)       = lookupSubst x s
  applySubst _ PUnit           = just Unit
  applySubst _ PVoid           = just Void
  applySubst _ PInt            = just Int
  applySubst _ PFloat          = just Float
  applySubst _ PStr            = just Str
  applySubst _ PBuffer         = just Buffer
  applySubst s (A P* B)        = maybe-pair _*_ (applySubst s A) (applySubst s B)
  applySubst s (A P+ B)        = maybe-pair _+_ (applySubst s A) (applySubst s B)
  applySubst s (A P⇒[ q ] B)   =
    maybe-pair (λ a b → a ⇒[ mk-kind q pure ] b) (applySubst s A) (applySubst s B)
  applySubst s (PEff A B)      =
    maybe-pair (λ a b → a ⇒[ mk-kind Many eff ] b) (applySubst s A) (applySubst s B)
  applySubst s (Pμ-type F)     = maybe-bind (λ f → just (μ-type f)) (applySubstFunctor s F)
  applySubst s (Pν-type F π)   = maybe-bind (λ f → just (ν-type f π)) (applySubstFunctor s F)

  applySubstFunctor : Subst → PolyFunctor → Maybe Functor
  applySubstFunctor s (PK A)   = maybe-bind (λ a → just (K a)) (applySubst s A)
  applySubstFunctor _ PId      = just Id
  applySubstFunctor s (F P⊕ G) =
    maybe-pair _⊕_ (applySubstFunctor s F) (applySubstFunctor s G)
  applySubstFunctor s (F P⊗ G) =
    maybe-pair _⊗_ (applySubstFunctor s F) (applySubstFunctor s G)


-- | For a polymorphic arrow schema `A ⇒[q] B` and a known ground
-- domain `Adom`, compute the ground codomain by matching `A`
-- against `Adom` (yielding a substitution) and applying it to `B`.
-- Plan 0.6.2 Phase 3b: the load-bearing primitive for classifier
-- helpers (e.g. `checkCompose`) that know one side of a poly
-- sub-expression's arrow type and need the other.
--
-- Returns `nothing` if the schema isn't an arrow, if the domain
-- doesn't match, or if the codomain still contains free TVars
-- after substitution (shouldn't happen with well-formed schemas).
schemaArrowCodomain : PolyType → Type → Maybe Type
schemaArrowCodomain (A P⇒[ _ ] B) domain =
  maybe-bind (λ subst → applySubst subst B) (instantiate A domain)
-- Schema is not an arrow → no codomain.
schemaArrowCodomain (PTVar _)    _ = nothing
schemaArrowCodomain PUnit        _ = nothing
schemaArrowCodomain PVoid        _ = nothing
schemaArrowCodomain (_ P* _)     _ = nothing
schemaArrowCodomain (_ P+ _)     _ = nothing
schemaArrowCodomain (PEff _ _)   _ = nothing
schemaArrowCodomain (Pμ-type _)  _ = nothing
schemaArrowCodomain (Pν-type _ _)  _ = nothing
schemaArrowCodomain PInt         _ = nothing
schemaArrowCodomain PFloat       _ = nothing
schemaArrowCodomain PStr         _ = nothing
schemaArrowCodomain PBuffer      _ = nothing
