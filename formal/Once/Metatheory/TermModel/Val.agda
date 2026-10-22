{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TermModel.Val — an environment, read at a variable it
-- holds (`val`). Forgetting other variables (`restrict`) does not change
-- what it holds at the ones it keeps, whichever proof forgets them; this is
-- what lets the substitution lemma compare environments built by different
-- chains of `restrict`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.TermModel.Val (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω; _+q_; _*q_)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩)
open import Once.Spec.Context
  using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; singleUse; zeroUsage; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_)
open import Once.Spec.Core.Meaning Σ fmt S using (Env; Slot; restrict; lookupᵛ)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameEnv)
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree)
open import Once.Metatheory.TermModel.Usage
open import Once.Metatheory.TermModel.Subst Σ S using (Thin; idθ; _θ*_; CThin; cid; ckeep; cskip; cdone)
open import Once.Metatheory.TermModel.Ren Σ fmt S using (ThinAgree)

-- The usage at a variable, and whether it holds one.
At : ∀ {n} → Usage n → Fin n → Quantity
At (q ∷ Ψ) zero    = q
At (q ∷ Ψ) (suc i) = At Ψ i

NZ : Quantity → Set
NZ Zero = ⊥
NZ One  = ⊤
NZ Many = ⊤

nz-irr : ∀ {q} (a b : NZ q) → a ≡ b
nz-irr {One}  a b = refl
nz-irr {Many} a b = refl

nz-≤ : ∀ {q₀ q} → q₀ ≤q q → NZ q₀ → NZ q
nz-≤ 1≤1 nz = tt
nz-≤ 1≤ω nz = tt
nz-≤ ω≤ω nz = tt

nz-mono : ∀ {n} {Ψ₀ Ψ : Usage n} → Ψ₀ ⊑ᵘ Ψ → ∀ i → NZ (At Ψ₀ i) → NZ (At Ψ i)
nz-mono (a ⊑∷ as) zero    nz = nz-≤ a nz
nz-mono (a ⊑∷ as) (suc i) nz = nz-mono as i nz

nz-single : ∀ {n} (i : Fin n) → NZ (At (singleUse i One) i)
nz-single zero    = tt
nz-single (suc i) = nz-single i

-- A usage counted through a substitution holds each replacement the
-- original holds.
private
  ≤q-trans′ : ∀ {a b c} → a ≤q b → b ≤q c → a ≤q c
  ≤q-trans′ 0≤q _   = 0≤q
  ≤q-trans′ 1≤1 b≤c = b≤c
  ≤q-trans′ 1≤ω ω≤ω = 1≤ω
  ≤q-trans′ ω≤ω ω≤ω = ω≤ω

  ⊑-trans′ : ∀ {n} {a b c : Usage n} → a ⊑ᵘ b → b ⊑ᵘ c → a ⊑ᵘ c
  ⊑-trans′ [] [] = []
  ⊑-trans′ (x ⊑∷ xs) (y ⊑∷ ys) = ≤q-trans′ x y ⊑∷ ⊑-trans′ xs ys

  ⊑-scale : ∀ {n} q (Ψ : Usage n) → NZ q → Ψ ⊑ᵘ q *ᵘ Ψ
  ⊑-scale One  []      nz = []
  ⊑-scale One  (p ∷ Ψ) nz = ≤q-refl p ⊑∷ ⊑-scale One Ψ nz
  ⊑-scale Many []      nz = []
  ⊑-scale Many (Zero ∷ Ψ) nz = 0≤q ⊑∷ ⊑-scale Many Ψ nz
  ⊑-scale Many (One  ∷ Ψ) nz = 1≤ω ⊑∷ ⊑-scale Many Ψ nz
  ⊑-scale Many (Many ∷ Ψ) nz = ω≤ω ⊑∷ ⊑-scale Many Ψ nz

·ᵐ-sup : ∀ {n n′} (Ψ : Usage n′) (Φ : Fin n′ → Usage n) i → NZ (At Ψ i) → Φ i ⊑ᵘ Ψ ·ᵐ Φ
·ᵐ-sup (q ∷ Ψ) Φ zero    nz = ⊑-trans′ (⊑-scale q (Φ zero) nz) (⊑ᵘ-+ˡ (q *ᵘ Φ zero) (Ψ ·ᵐ λ i → Φ (suc i)))
·ᵐ-sup (q ∷ Ψ) Φ (suc i) nz = ⊑-trans′ (·ᵐ-sup Ψ (λ i → Φ (suc i)) i nz) (⊑ᵘ-+ʳ (q *ᵘ Φ zero) (Ψ ·ᵐ λ i → Φ (suc i)))

module _ {m : ℕ} (σ : TySub m 0) where

  slotVal : ∀ q {X : Set} → Slot q X → NZ q → X
  slotVal One  v nz = v
  slotVal Many v nz = v

  val : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} → Env σ Γ Ψ → (i : Fin n) → NZ (At Ψ i) → ⟦ lookup Γ i ⟨ σ ⟩ ⟧ᵛ
  val {Γ = Γ ▸ A} {q ∷ Ψ} (γ , v) zero    nz = slotVal q v nz
  val {Γ = Γ ▸ A} {q ∷ Ψ} (γ , v) (suc i) nz = val γ i nz

  val-irr : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) i (a b : NZ (At Ψ i)) → val γ i a ≡ val γ i b
  val-irr γ i a b = cong (val γ i) (nz-irr a b)

  restrict-val : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ : Usage n} (p : Ψ₀ ⊑ᵘ Ψ) (γ : Env σ Γ Ψ) i (nz : NZ (At Ψ₀ i))
               → val (restrict σ p γ) i nz ≡ val γ i (nz-mono p i nz)
  restrict-val {Γ = Γ ▸ A} (1≤1 ⊑∷ p) (γ , v) zero nz = refl
  restrict-val {Γ = Γ ▸ A} (1≤ω ⊑∷ p) (γ , v) zero nz = refl
  restrict-val {Γ = Γ ▸ A} (ω≤ω ⊑∷ p) (γ , v) zero nz = refl
  restrict-val {Γ = Γ ▸ A} (0≤q ⊑∷ p) (γ , v) (suc i) nz = restrict-val p γ i nz
  restrict-val {Γ = Γ ▸ A} (1≤1 ⊑∷ p) (γ , v) (suc i) nz = restrict-val p γ i nz
  restrict-val {Γ = Γ ▸ A} (1≤ω ⊑∷ p) (γ , v) (suc i) nz = restrict-val p γ i nz
  restrict-val {Γ = Γ ▸ A} (ω≤ω ⊑∷ p) (γ , v) (suc i) nz = restrict-val p γ i nz

  lookup-val : ∀ {n} (Γ : Ctx m n) (i : Fin n) (γ : Env σ Γ (singleUse i One)) → lookupᵛ σ Γ i γ ≡ val γ i (nz-single i)
  lookup-val (Γ ▸ A) zero    (γ , v) = refl
  lookup-val (Γ ▸ A) (suc i) (γ , v) = lookup-val Γ i γ

  -- The Spec's self-sameness, read at variables.
  SelfSame : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} → Env σ Γ Ψ → Set
  SelfSame {Γ = Γ} γ = ∀ i nz → Same (lookup Γ i ⟨ σ ⟩) (val γ i nz) (val γ i nz)

  selfSame : ∀ {n} (Γ : Ctx m n) (Ψ : Usage n) (γ : Env σ Γ Ψ) → SameEnv Σ fmt S σ Γ Ψ γ → SelfSame γ
  selfSame (Γ ▸ A) (Zero ∷ Ψ) (γ , v) e        zero    ()
  selfSame (Γ ▸ A) (One  ∷ Ψ) (γ , v) (e , sv) zero    nz = sv
  selfSame (Γ ▸ A) (Many ∷ Ψ) (γ , v) (e , sv) zero    nz = sv
  selfSame (Γ ▸ A) (Zero ∷ Ψ) (γ , v) e        (suc i) nz = selfSame Γ Ψ γ e i nz
  selfSame (Γ ▸ A) (One  ∷ Ψ) (γ , v) (e , sv) (suc i) nz = selfSame Γ Ψ γ e i nz
  selfSame (Γ ▸ A) (Many ∷ Ψ) (γ , v) (e , sv) (suc i) nz = selfSame Γ Ψ γ e i nz

  selfSame-restrict : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ : Usage n} (p : Ψ₀ ⊑ᵘ Ψ) {γ : Env σ Γ Ψ} → SelfSame γ → SelfSame (restrict σ p γ)
  selfSame-restrict p {γ} ss i nz =
    subst (λ w → Same _ w w) (sym (restrict-val p γ i nz)) (ss i (nz-mono p i nz))

  -- Two environments that hold the same values agree along the identity.
  thin-cid : ∀ {n} (Γ : Ctx m n) {Ψ′ Ψ : Usage n} {γ′ : Env σ Γ Ψ′} {γ : Env σ Γ Ψ}
           → (∀ i nz′ nz → Same (lookup Γ i ⟨ σ ⟩) (val γ′ i nz′) (val γ i nz))
           → ThinAgree σ (cid Γ) Ψ′ Ψ γ′ γ
  thin-cid ∅ {[]} {[]} h = tt
  thin-cid (Γ ▸ A) {q′ ∷ Ψ′} {q ∷ Ψ} {γ′ , v′} {γ , v} h = thin-cid Γ (λ i → h (suc i)) , slot q′ q v′ v (h zero)
    where
      slot : ∀ q′ q v′ v → (∀ nz′ nz → Same (A ⟨ σ ⟩) (slotVal q′ v′ nz′) (slotVal q v nz)) → SlotAgree σ A q′ q v′ v
      slot Zero q    v′ v k = tt
      slot One  Zero v′ v k = tt
      slot Many Zero v′ v k = tt
      slot One  One  v′ v k = k tt tt
      slot One  Many v′ v k = k tt tt
      slot Many One  v′ v k = k tt tt
      slot Many Many v′ v k = k tt tt
