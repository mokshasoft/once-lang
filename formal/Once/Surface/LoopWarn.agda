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

-- how many loops in a term have a pure round
silentLoops : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {T : Ty m} → Expr Γ Ψ T → ℕ
silentLoops (lam _ _ b)      = silentLoops b
silentLoops (app f x)        = silentLoops f + silentLoops x
silentLoops (effApp f x)     = silentLoops f + silentLoops x
silentLoops (pair a b)       = silentLoops a + silentLoops b
silentLoops (fst' e)         = silentLoops e
silentLoops (snd' e)         = silentLoops e
silentLoops (inl' e)         = silentLoops e
silentLoops (inr' e)         = silentLoops e
silentLoops (case' s f g)    = silentLoops s + (silentLoops f + silentLoops g)
silentLoops (absurd e)       = silentLoops e
silentLoops (let' a b)       = silentLoops a + silentLoops b
silentLoops (add a b)        = silentLoops a + silentLoops b
silentLoops (sub a b)        = silentLoops a + silentLoops b
silentLoops (mul a b)        = silentLoops a + silentLoops b
silentLoops (fadd a b)       = silentLoops a + silentLoops b
silentLoops (fsub a b)       = silentLoops a + silentLoops b
silentLoops (fmul a b)       = silentLoops a + silentLoops b
silentLoops (fdiv a b)       = silentLoops a + silentLoops b
silentLoops (i2f e)          = silentLoops e
silentLoops (div a b)        = silentLoops a + silentLoops b
silentLoops (mod' a b)       = silentLoops a + silentLoops b
silentLoops (neg e)          = silentLoops e
silentLoops (lt a b)         = silentLoops a + silentLoops b
silentLoops (le a b)         = silentLoops a + silentLoops b
silentLoops (gt a b)         = silentLoops a + silentLoops b
silentLoops (ge a b)         = silentLoops a + silentLoops b
silentLoops (eq a b)         = silentLoops a + silentLoops b
silentLoops (ne a b)         = silentLoops a + silentLoops b
silentLoops (coerce _ e)     = silentLoops e
silentLoops (closed e)       = silentLoops e
silentLoops (morph-app _ e)  = silentLoops e
silentLoops (comp' f g)      = silentLoops f + silentLoops g
silentLoops (copair' f g)    = silentLoops f + silentLoops g
silentLoops (fork' f g)      = silentLoops f + silentLoops g
silentLoops (curry' f)       = silentLoops f
silentLoops (cata _ a)       = silentLoops a
silentLoops (ana _ c)        = silentLoops c
silentLoops (loop r)         = (if roundIsPure r then 1 else 0) + silentLoops r
{-# CATCHALL #-}
silentLoops _                = 0
