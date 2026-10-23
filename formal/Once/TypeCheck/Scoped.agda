-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Scoped — the checker's scope as the Spec names it (plan
-- 0.122 §2b-3, stage d).
--
-- The checker's locals — names over a de Bruijn context — are the Spec's
-- `Locals` (`LocalsOf`), and a name the checker finds there is the Spec's
-- local of that type at that index (`found`).
------------------------------------------------------------------------

module Once.TypeCheck.Scoped where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
import Once.Spec.Grade as LG
import Once.Spec.Context as SCx
open import Once.Spec.Surface.Syntax
open import Once.Internal.Context using (svar; SVar)
open import Once.Internal.Typing.Scope using (Binding; lookupLocal-go; lookupLocal-at; lookupLocal-next)
open Binding using (name)
import Once.Spec.Surface.Typing as SUT

------------------------------------------------------------------------
-- The locals
------------------------------------------------------------------------

module Locals (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) {m : ℕ} where

  open SUT Σ S nm using (Locals; ∅; _▹_∶_; _∋_⦂_at_; here; there)

  data LocalsOf : ∀ {n} → List (Binding m) → SCx.Ctx m n → Locals m n → Set where
    lo-∅ : LocalsOf [] SCx.∅ ∅
    lo-▸ : ∀ {n} {Γn} {Γd : SCx.Ctx m n} {L b A} → LocalsOf Γn Γd L → LocalsOf (b ∷ Γn) (Γd SCx.▸ A) (L ▹ name b ∶ A)

  private
    -- the index a lookup found
    idx : ∀ {n} {Γd : SCx.Ctx m n} → Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] SVar Γd Ψ A) → Maybe (Fin n)
    idx nothing                 = nothing
    idx (just (_ , _ , svar i)) = just i

    zero≢suc : ∀ {n} {i : Fin n} → zero ≡ suc i → ⊥
    zero≢suc ()

    suc-inj : ∀ {n} {i j : Fin n} → suc i ≡ suc j → i ≡ j
    suc-inj refl = refl

    next-zero : ∀ {n} {Γd : SCx.Ctx m n} {B} (r : Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] SVar Γd Ψ A))
              → lookupLocal-next {B = B} r ≡ just (SCx.lookup (Γd SCx.▸ B) zero , SCx.singleUse zero LG.One , svar zero) → ⊥
    next-zero nothing ()
    next-zero (just (_ , _ , svar j)) e = zero≢suc (sym (just-injective (cong idx e)))

    next-suc : ∀ {n} {Γd : SCx.Ctx m n} {B} (r : Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] SVar Γd Ψ A)) (i : Fin n)
             → lookupLocal-next {B = B} r ≡ just (SCx.lookup (Γd SCx.▸ B) (suc i) , SCx.singleUse (suc i) LG.One , svar (suc i))
             → r ≡ just (SCx.lookup Γd i , SCx.singleUse i LG.One , svar i)
    next-suc nothing i ()
    next-suc {Γd = Γd} (just (_ , _ , svar j)) i e =
      cong (λ k → just (SCx.lookup Γd k , SCx.singleUse k LG.One , svar k)) (suc-inj (just-injective (cong idx e)))

    next-nothing : ∀ {n} {Γd : SCx.Ctx m n} {B} (r : Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] SVar Γd Ψ A))
                 → lookupLocal-next {B = B} r ≡ nothing → r ≡ nothing
    next-nothing nothing                 e = refl
    next-nothing (just (_ , _ , svar i)) ()

  -- A name the checker finds is the Spec's local, at the type the context gives.
  found : ∀ {n x} {Γn} {Γd : SCx.Ctx m n} {L} → LocalsOf Γn Γd L → (i : Fin n)
        → lookupLocal-go x Γn Γd ≡ just (SCx.lookup Γd i , SCx.singleUse i LG.One , svar i)
        → L ∋ x ⦂ SCx.lookup Γd i at i
  found-at : ∀ {n x} {b} {Γn} {Γd : SCx.Ctx m n} {L A} → LocalsOf Γn Γd L → (i : Fin (ℕ.suc n))
           → (d : Dec (x ≡ name b))
           → lookupLocal-at x b Γn Γd {B = A} d ≡ just (SCx.lookup (Γd SCx.▸ A) i , SCx.singleUse i LG.One , svar i)
           → (L ▹ name b ∶ A) ∋ x ⦂ SCx.lookup (Γd SCx.▸ A) i at i
  found lo-∅ () eq
  found {x = x} (lo-▸ {b = b} lo) i eq = found-at lo i (x ≟ name b) eq
  found-at {b = b} {L = L} {A = A} lo zero (yes e) eq = subst (λ y → (L ▹ name b ∶ A) ∋ y ⦂ A at zero) (sym e) here
  found-at lo (suc i) (yes e) eq = ⊥-elim′ (zero≢suc (just-injective (cong idx eq)))
    where ⊥-elim′ : ⊥ → _
          ⊥-elim′ ()
  found-at {x = x} {Γn = Γn} {Γd} lo zero (no ¬e) eq = ⊥-elim′ (next-zero (lookupLocal-go x Γn Γd) eq)
    where ⊥-elim′ : ⊥ → _
          ⊥-elim′ ()
  found-at {x = x} {Γn = Γn} {Γd} lo (suc i) (no ¬e) eq = there ¬e (found lo i (next-suc (lookupLocal-go x Γn Γd) i eq))
