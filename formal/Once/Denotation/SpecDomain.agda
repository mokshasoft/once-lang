{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.SpecDomain — the Spec's value domain, read at a closed
-- instance `σ` of no type variables (plan 0.122 §5.5 M2).
--
-- The bridge to the implementation (`Adequacy.MeaningBridge`) reads values
-- in the Spec's domain (`Spec.Domain Σ`, graded by `Spec.Effect Σ`). The Spec
-- states its meaning at an instance `σ` (`Spec.Core.Meaning`), so a ground
-- type `A` is read as `A ⟨ σ ⟩`: then a value of a ground type and the Spec's
-- core meaning at it have the same type. Over it: the grade's monad, the
-- recursion formers' operations and the subtyping conversions as the Spec's
-- core meaning has them, the environment over the variables a term uses, and
-- the crossing of a ground type read over type variables (`wk₀`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Type using (TySub)

module Once.Denotation.SpecDomain (Σ : Signature) (σ : TySub 0 0) where

open import Data.Fin using (Fin)
import Data.Fin
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; Finite; fin; _⊑π_)
open import Once.Spec.Type using (Ty; Type; Fun; KCtx; WFFun; _⟨_⟩; _⟨_⟩F; μ; ν)
import Once.Spec.Type as SpT
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Context using ([]; _∷_; _⊑∷_; _▸_)
import Once.Spec.Context
open import Once.Internal.Context using (Ctx; Usage; lookup; ∅; ⟦_⟧ᶜ; _↾_; _⊑ᵘ_; ⊑[]; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; singleUse)
open import Once.Internal.Type using (wk₀)
open import Once.Internal.Weaken using (wk₀-id)
open import Once.Spec.Polynomial using (inS)
import Once.Spec.Effect Σ as SE
open SE.νM using (outν)
import Once.Spec.Domain Σ as SD

------------------------------------------------------------------------
-- The values of a ground type, at σ
------------------------------------------------------------------------

⟦_⟧ᵛ : Type → Set
⟦ A ⟧ᵛ = SD.⟦ A ⟨ σ ⟩ ⟧ᵛ

-- A ground type read over no type variables means what it means.
⟦wk₀⟧ᵛ : (A : Type) → ⟦ wk₀ {0} A ⟧ᵛ ≡ ⟦ A ⟧ᵛ
⟦wk₀⟧ᵛ A = cong ⟦_⟧ᵛ (wk₀-id A)

------------------------------------------------------------------------
-- The grade's monad
------------------------------------------------------------------------

M : Purity → Set → Set
M = SE.M

bindM : ∀ π {X Y} → M π X → (X → M π Y) → M π Y
bindM = SE.bind

fmapM : ∀ π {X Y} → (X → Y) → M π X → M π Y
fmapM = SE.fmap

subM : ∀ {π π′} → π ⊑π π′ → ∀ {X} → M π X → M π′ X
subM = SE.sub

-- The unit of a grade (`pure ⊑π π`): a pure value, subeffected.
returnM : ∀ {π} → pure ⊑π π → ∀ {X} → X → M π X
returnM u x = SE.sub u x

------------------------------------------------------------------------
-- The recursion formers, as the Spec's core meaning has them
------------------------------------------------------------------------

in-valueᵛ : ∀ {Δₖ : KCtx 0} {F : Fun 0} → WFFun Δₖ F → ⟦ SpT.⟦ F ⟧F (μ F) ⟧ᵛ → ⟦ μ F ⟧ᵛ
in-valueᵛ {F = F} wf x = inS (SD.toL σ F (μ F) x)

-- The fold (the unit `u` is the surface rule's; the Spec's fold needs none).
cata-semᵛ : ∀ {Δₖ : KCtx 0} {π} → pure ⊑π π → ∀ {A : Type} {F : Fun 0} → WFFun Δₖ F
          → (⟦ SpT.⟦ F ⟧F A ⟧ᵛ → M π ⟦ A ⟧ᵛ) → ⟦ μ F ⟧ᵛ → M π ⟦ A ⟧ᵛ
cata-semᵛ {π = π} u {A = A} {F = F} wf alg = SD.foldM π (SD.code (F ⟨ σ ⟩F)) (λ l → alg (SD.fromL σ F A l))

-- `unfold c s` at coalgebra grade `φ`, given the coalgebra's function: the
-- stream, each forced layer running the coalgebra.
ana-semᵛ : ∀ {Δₖ : KCtx 0} {A : Type} {F : Fun 0} (φ : Finite) → WFFun Δₖ F
         → (⟦ A ⟧ᵛ → M (fin φ) ⟦ SpT.⟦ F ⟧F A ⟧ᵛ) → ⟦ A ⟧ᵛ → ⟦ ν F φ ⟧ᵛ
ana-semᵛ {A = A} {F = F} φ wf clo = SE.ana φ (SD.code (F ⟨ σ ⟩F)) (λ x → SE.fmap (fin φ) (SD.toL σ F A) (clo x))

-- Forcing a layer of a stream.
out-semᵛ : ∀ {Δₖ : KCtx 0} φ {F : Fun 0} → WFFun Δₖ F → ⟦ ν F φ ⟧ᵛ → M (fin φ) ⟦ SpT.⟦ F ⟧F (ν F φ) ⟧ᵛ
out-semᵛ φ {F} wf v = SE.fmap (fin φ) (SD.fromL σ F (ν F φ)) (outν v)

-- A subtyping derivation's conversion.
⟦_⟧<:ᵛ : ∀ {A B : Type} → A <: B → ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ
⟦ p ⟧<:ᵛ = SD.conv σ p

-- The server loop.
loop : ∀ {A B : Set} → (A → SE.T (B ⊎ A)) → A → SE.T∞ B
loop = SE.loop

------------------------------------------------------------------------
-- The environment: the values of the variables a term uses
------------------------------------------------------------------------

lookupᵛUsed : ∀ {n} (Γ : Ctx 0 n) (i : Fin n) → ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⟧ᵛ → ⟦ lookup Γ i ⟧ᵛ
lookupᵛUsed (Γ ▸ A) Data.Fin.zero    dγ = proj₂ dγ
lookupᵛUsed (Γ ▸ A) (Data.Fin.suc i) dγ = lookupᵛUsed Γ i dγ

restrictᵛ : ∀ {n} {Γ : Ctx 0 n} {Ψ Ψ' : Usage n} → Ψ' ⊑ᵘ Ψ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᵛ → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᵛ
restrictᵛ {Γ = ∅}     ⊑[]          dγ = dγ
restrictᵛ {Γ = Γ ▸ A} (z≤z ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule dγ
restrictᵛ {Γ = Γ ▸ A} (z≤o ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ)
restrictᵛ {Γ = Γ ▸ A} (z≤m ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ)
restrictᵛ {Γ = Γ ▸ A} (o≤o ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ
restrictᵛ {Γ = Γ ▸ A} (o≤m ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ
restrictᵛ {Γ = Γ ▸ A} (m≤m ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ

bindᵛ : ∀ {n} {Γ : Ctx 0 n} {Ψ' : Usage n} {A : Type} (q : Quantity)
      → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᵛ → ⟦ A ⟧ᵛ → ⟦ ⟦ (Γ ▸ A) ↾ (q ∷ Ψ') ⟧ᶜ ⟧ᵛ
bindᵛ Zero dγ a = dγ
bindᵛ One  dγ a = dγ , a
bindᵛ Many dγ a = dγ , a

bindᵛ0 : ∀ {n} {Γ : Ctx 0 n} {Ψ' : Usage n} {A : Type}
       → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᵛ → ⟦ ⟦ (Γ ▸ A) ↾ (Zero ∷ Ψ') ⟧ᶜ ⟧ᵛ
bindᵛ0 dγ = dγ

eraseᵛ : ∀ {n} (Γ : Ctx 0 n) (Ψ : Usage n) → ⟦ ⟦ Γ ⟧ᶜ ⟧ᵛ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᵛ
eraseᵛ ∅       []         dγ = dγ
eraseᵛ (Γ ▸ A) (Zero ∷ Ψ) dγ = eraseᵛ Γ Ψ (proj₁ dγ)
eraseᵛ (Γ ▸ A) (One  ∷ Ψ) dγ = eraseᵛ Γ Ψ (proj₁ dγ) , proj₂ dγ
eraseᵛ (Γ ▸ A) (Many ∷ Ψ) dγ = eraseᵛ Γ Ψ (proj₁ dγ) , proj₂ dγ

env0 : ∀ {Ψ : Usage 0} → ⟦ ⟦ Once.Spec.Context.∅ {0} ⟧ᶜ ⟧ᵛ → ⟦ ⟦ Once.Spec.Context.∅ {0} ↾ Ψ ⟧ᶜ ⟧ᵛ
env0 {Ψ = []} dγ = dγ
