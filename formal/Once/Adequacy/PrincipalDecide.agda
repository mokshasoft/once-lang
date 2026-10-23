-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.PrincipalDecide — the compiler DECIDES principality
-- (plan 0.119 D6, D314/D321).
--
-- `Compile.firstChecking ctx e Xs` runs the verified checker at each type of
-- `Xs`. It finds none exactly when the body checks at none of them: the
-- checker is sound (a success carries a derivation) and complete
-- (`check-complete`: a derivation means a success).
------------------------------------------------------------------------

module Once.Adequacy.PrincipalDecide where

open import Once.Spec.Type using (Ty)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Relation.Nullary using (¬_)
open import Once.Spec.Type using (Type)
open import Once.Internal.Syntax using (RawExpr)
open import Once.Internal.Typing.Scope using (NamedCtx)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_)
open import Once.Internal.Context using (Usage; Ctx)
import Once.Compile as C
import Once.TypeCheck.Elaborate as TE
open import Once.TypeCheck.Completeness using (check-complete)

-- a check result's failure, as a Boolean
fails : ∀ {m} {n} {Γ : Ctx m n} {A : Ty m} → TE.CheckElabResult Γ A → Bool
fails (TE.failure _)         = true
fails (TE.success _ _ _ _)   = false

firstChecking-sound : ∀ {m} (ctx : NamedCtx m) (e : RawExpr) (Xs : List (Ty m))
                    → C.firstChecking ctx e Xs ≡ nothing
                    → ∀ {X} → X ∈ Xs → ∀ {Ψ : Usage (NamedCtx.size ctx)} → ¬ (ctx ⊢ᶜ e ∶ X ⨾ Ψ)
fc-step-sound : ∀ {m} (ctx : NamedCtx m) (e : RawExpr) (X : Ty m) (Xs : List (Ty m))
                (r : TE.VerifiedCheckResult ctx e X) → TE.checkElabV ctx e X ≡ r
              → C.fc-step ctx e X Xs r ≡ nothing
              → ∀ {Y} → Y ∈ (X ∷ Xs) → ∀ {Ψ : Usage (NamedCtx.size ctx)} → ¬ (ctx ⊢ᶜ e ∶ Y ⨾ Ψ)

firstChecking-sound ctx e []       eq ()
firstChecking-sound ctx e (X ∷ Xs) eq m = fc-step-sound ctx e X Xs (TE.checkElabV ctx e X) refl eq m

fc-step-sound ctx e X Xs (TE.success _ _ _ _ , _) r≡ ()
fc-step-sound ctx e X Xs (TE.failure err , _) r≡ eq (here refl) d =
  case cong fails (trans (sym (cong proj₁ r≡)) (proj₂ (proj₂ (proj₂ (check-complete d))))) of λ ()
fc-step-sound ctx e X Xs (TE.failure err , _) r≡ eq (there m) d = firstChecking-sound ctx e Xs eq m d

firstChecking-complete : ∀ {m} (ctx : NamedCtx m) (e : RawExpr) (Xs : List (Ty m))
                       → (∀ {X} → X ∈ Xs → ∀ {Ψ : Usage (NamedCtx.size ctx)} → ¬ (ctx ⊢ᶜ e ∶ X ⨾ Ψ))
                       → C.firstChecking ctx e Xs ≡ nothing
fc-step-complete : ∀ {m} (ctx : NamedCtx m) (e : RawExpr) (X : Ty m) (Xs : List (Ty m))
                   (r : TE.VerifiedCheckResult ctx e X)
                 → (∀ {Y} → Y ∈ (X ∷ Xs) → ∀ {Ψ : Usage (NamedCtx.size ctx)} → ¬ (ctx ⊢ᶜ e ∶ Y ⨾ Ψ))
                 → C.fc-step ctx e X Xs r ≡ nothing

firstChecking-complete ctx e []       h = refl
firstChecking-complete ctx e (X ∷ Xs) h = fc-step-complete ctx e X Xs (TE.checkElabV ctx e X) h

fc-step-complete ctx e X Xs (TE.success _ _ _ _ , w) h with h (here refl) (proj₁ w)
... | ()
fc-step-complete ctx e X Xs (TE.failure _ , _) h = firstChecking-complete ctx e Xs (λ m → h (there m))
