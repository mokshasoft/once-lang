-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.ContractLaws — the lemmas about `Once.Spec.Contract`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free).
------------------------------------------------------------------------

module Once.Spec.ContractLaws where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String) renaming (_≟_ to _≟ˢ_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Membership.DecPropositional as DecMem
open import Once.Type using (Type; _⇒[_]_; mk-kind; Zero; One; Many; Void; isVoid?; isUnit?) renaming (Unit to UnitT)
import Once.Type as Ty
open import Once.Type.DecEq using (_≟T_)
open import Data.Empty using (⊥-elim)
open import Once.Functor.Translate using (IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid)
open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier Carrier as M
open import Once.Denotation.Trace using (SigOpEvent)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.Spec.Contract
open Key
open Impl

-- A decision on a membership that holds is `yes` (of the decided proof).
yes-of : ∀ {k ks} → k ∈ ks → Σ (k ∈ ks) (λ p₀ → (k ∈K? ks) ≡ yes p₀)

yes-of {k} {ks} p = go (k ∈K? ks)
  where go : (d : Dec (k ∈ ks)) → Σ (k ∈ ks) (λ p₀ → d ≡ yes p₀)
        go (yes p₀) = p₀ , refl
        go (no ¬p)  = ⊥-elim (¬p p)

-- A declaration's key is declared.
private
  value-there : ∀ {k ks} (ct : Contract) → k ∈ ks → k ∈ value-step ct ks
  value-there (value _)   m = there m
  value-there (answers _) m = m
  value-there effect      m = m
  answer-there : ∀ {k ks} (ct : Contract) → k ∈ ks → k ∈ answer-step ct ks
  answer-there (value _)   m = m
  answer-there (answers _) m = there m
  answer-there effect      m = m

value-∈ : ∀ {Σ x T k} → (x , T) ∈ Σ → contractOf x T ≡ value k → k ∈ valueKeys Σ

value-∈ {(c , T) ∷ Σ} (here refl) eq rewrite eq = here refl

value-∈ {(c , T) ∷ Σ} (there m)   eq = value-there (contractOf c T) (value-∈ m eq)

answer-∈ : ∀ {Σ x T k} → (x , T) ∈ Σ → contractOf x T ≡ answers k → k ∈ answerKeys Σ

answer-∈ {(c , T) ∷ Σ} (here refl) eq rewrite eq = here refl

answer-∈ {(c , T) ∷ Σ} (there m)   eq = answer-there (contractOf c T) (answer-∈ m eq)

-- A first-order constant (not an arrow) is a value contract at `Unit → A`.
base-contract : ∀ {A} (x : String) → IsBaseType A → contractOf x A ≡ value (key x UnitT A)

base-contract x base-Unit        = refl

base-contract x base-Void        = refl

base-contract x base-Int         = refl

base-contract x base-Float       = refl

base-contract x (base-Prod a b)  = refl

base-contract x (base-Sum a b)   = refl

base-contract x base-rigid       = refl
