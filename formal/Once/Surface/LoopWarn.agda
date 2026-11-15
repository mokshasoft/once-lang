-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.LoopWarn — A ROUND THAT PERFORMS NO EVENT (plan 0.119 D5).
--
-- GOAL.md: a loop whose round performs no event is a correct program that
-- may be useless — if it never ends, it goes silent forever. The compiler
-- says so. A round performs no event when its arrow is PURE: the checker
-- then elaborates it at the loop's `act` arrow through a coercion from the
-- pure arrow it has (`c-sub`), so the elaborated term says it.
--
-- A WARNING, NOT A JUDGMENT: a round that is `act` by its type and still
-- performs no event (an effectful-typed lambda whose body happens to be pure)
-- is not reported. What is reported is always true.
------------------------------------------------------------------------

module Once.Surface.LoopWarn where

open import Once.Spec.Type using (Ty)
open import Once.Spec.Context using (Ctx; Usage)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _+_)
open import Once.Spec.Grade using (mk-kind; pure)
open import Once.Spec.Type using (Type; _⇒[_]_)
open import Once.Surface.Syntax using (Expr)
open import Once.Spec.Theory using (float-equality; ‵==; ‵!=)
open Once.Surface.Syntax.Expr

-- a pure arrow
pureArrow : ∀ {m} → Ty m → Bool
pureArrow (_ ⇒[ mk-kind _ pure ] _) = true
{-# CATCHALL #-}
pureArrow _ = false

-- a round coerced from a pure arrow
roundIsPure : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {T : Ty m} → Expr Γ Ψ T → Bool
roundIsPure (coerce {A = S} _ _) = pureArrow S
{-# CATCHALL #-}
roundIsPure _ = false

-- | A count over a term: each node's own contribution (`here`), summed over
-- the whole term. The warnings are counts of this shape, so they share the walk.
Here : Set
Here = ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {T : Ty m} → Expr Γ Ψ T → ℕ

exprCount : Here → ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {T : Ty m} → Expr Γ Ψ T → ℕ
exprCount h e = h e + below e
  where
    below : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {T : Ty m} → Expr Γ Ψ T → ℕ
    below (lam _ _ b)      = exprCount h b
    below (app f x)        = exprCount h f + exprCount h x
    below (effApp f x)     = exprCount h f + exprCount h x
    below (pair a b)       = exprCount h a + exprCount h b
    below (fst' e)         = exprCount h e
    below (snd' e)         = exprCount h e
    below (inl' e)         = exprCount h e
    below (inr' e)         = exprCount h e
    below (case' s f g)    = exprCount h s + (exprCount h f + exprCount h g)
    below (absurd e)       = exprCount h e
    below (let' a b)       = exprCount h a + exprCount h b
    below (num _ _ e)      = exprCount h e
    below (coerce _ e)     = exprCount h e
    below (closed e)       = exprCount h e
    below (morph-app _ e)  = exprCount h e
    below (comp' f g)      = exprCount h f + exprCount h g
    below (copair' f g)    = exprCount h f + exprCount h g
    below (fork' f g)      = exprCount h f + exprCount h g
    below (curry' f)       = exprCount h f
    below (cata _ a)       = exprCount h a
    below (ana _ c)        = exprCount h c
    below (loop r)         = exprCount h r
    {-# CATCHALL #-}
    below _                = 0

-- how many loops in a term have a pure round
silentLoops : Here
silentLoops = exprCount here
  where
    here : Here
    here (loop r) = if roundIsPure r then 1 else 0
    {-# CATCHALL #-}
    here _        = 0

-- | Plan 0.150 step 5: how many `==` / `!=` a term applies directly at
-- `Float` — identity, where IEEE equality is `==.` / `!=.`. A use through a
-- generic definition is that definition's (`poly`), so it is not counted.
floatIdentityEqs : Here
floatIdentityEqs = exprCount here
  where
    here : Here
    here (num float-equality ‵== _) = 1
    here (num float-equality ‵!= _) = 1
    {-# CATCHALL #-}
    here _                          = 0
