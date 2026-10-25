-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.PrincipalDecide — the compiler DECIDES principality
-- (plan 0.119 D6, D314/D321).
--
-- `Compile.firstChecking ctx e Xs` runs the verified checker at each type of
-- `Xs`. It finds none exactly when the checker rejects the body at each of
-- them (`Principal.PrincipalAt`'s condition).
------------------------------------------------------------------------

module Once.Adequacy.PrincipalDecide where

open import Once.Spec.Type using (Ty)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.Internal.Typing.Scope using (NamedCtx)
open import Once.Internal.Principal using (Fails; fails)
import Once.Compile as C
import Once.TypeCheck.Elaborate as TE

firstChecking-sound : ∀ {m} (ctx : NamedCtx m) (e : Expr) (Xs : List (Ty m))
                    → C.firstChecking ctx e Xs ≡ nothing
                    → ∀ {X} → X ∈ Xs → Fails (proj₁ (TE.checkElabV ctx e X))
fc-step-sound : ∀ {m} (ctx : NamedCtx m) (e : Expr) (X : Ty m) (Xs : List (Ty m))
                (r : TE.VerifiedCheckResult ctx e X) → TE.checkElabV ctx e X ≡ r
              → C.fc-step ctx e X Xs r ≡ nothing
              → ∀ {Y} → Y ∈ (X ∷ Xs) → Fails (proj₁ (TE.checkElabV ctx e Y))

firstChecking-sound ctx e []       eq ()
firstChecking-sound ctx e (X ∷ Xs) eq m = fc-step-sound ctx e X Xs (TE.checkElabV ctx e X) refl eq m

fc-step-sound ctx e X Xs (TE.success _ _ _ _ , _) r≡ ()
fc-step-sound ctx e X Xs (TE.failure err , _) r≡ eq (here refl) rewrite r≡ = fails
fc-step-sound ctx e X Xs (TE.failure err , _) r≡ eq (there m) = firstChecking-sound ctx e Xs eq m

firstChecking-complete : ∀ {m} (ctx : NamedCtx m) (e : Expr) (Xs : List (Ty m))
                       → (∀ {X} → X ∈ Xs → Fails (proj₁ (TE.checkElabV ctx e X)))
                       → C.firstChecking ctx e Xs ≡ nothing
fc-step-complete : ∀ {m} (ctx : NamedCtx m) (e : Expr) (X : Ty m) (Xs : List (Ty m))
                   (r : TE.VerifiedCheckResult ctx e X) → Fails (proj₁ r)
                 → (∀ {Y} → Y ∈ Xs → Fails (proj₁ (TE.checkElabV ctx e Y)))
                 → C.fc-step ctx e X Xs r ≡ nothing

firstChecking-complete ctx e []       h = refl
firstChecking-complete ctx e (X ∷ Xs) h = fc-step-complete ctx e X Xs (TE.checkElabV ctx e X) (h (here refl)) (λ m → h (there m))

fc-step-complete ctx e X Xs (TE.failure _ , _) fails h = firstChecking-complete ctx e Xs h
