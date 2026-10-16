{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TermModel.Ren — renaming, in the meaning: a term renamed
-- along a thinning, run in an environment that agrees with the original
-- one at the kept variables, means a computation related to the original's.
-- (Weakening is the case the substitution lemma needs.)
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.TermModel.Ren (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Grade
  using (Quantity; Zero; One; Many; Purity; pure; act; fin; mk-kind; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type
  using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; respects-∘; ⟨⟩-∘; _⟨_⟩; _⟨_⟩F; Int; Float; _⇒[_]_; _*_; _+_; μ; ν; ⟦_⟧F; Unit)
open import Once.Spec.Context using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_;
                                     ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; fmap; module νM)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs)
open import Once.Metatheory.Erase Σ using (toT∞-fmap)
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ
open import Once.Metatheory.Coherence.Loop Σ using (loopSame)
open import Once.Metatheory.Coherence.Conv Σ using (convSame)
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree)
open import Once.Metatheory.Coherence.Leaves Σ fmt S using (sigopRefl; primSame; substSame; slotSame; caseRel)
open import Once.Metatheory.TermModel.Usage
open import Once.Metatheory.TermModel.Subst Σ S

open DefSem

module _ {m : ℕ} (σ : TySub m 0) where

  ThinAgree : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} → CThin θ Γ Γ′
            → (Ψ′ : Usage n′) (Ψ : Usage n) → Env σ Γ′ Ψ′ → Env σ Γ Ψ → Set
  ThinAgree cdone [] [] γ′ γ = ⊤
  ThinAgree (ckeep {A = A} c) (q′ ∷ Ψ′) (q ∷ Ψ) (γ′ , v′) (γ , v) = ThinAgree c Ψ′ Ψ γ′ γ × SlotAgree σ A q′ q v′ v
  ThinAgree (cskip c) (q′ ∷ Ψ′) Ψ (γ′ , v′) γ = ThinAgree c Ψ′ Ψ γ′ γ

  thinRestrictˡ : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} (c : CThin θ Γ Γ′) {Ψ₀′ Ψ′ : Usage n′} {Ψ : Usage n} (P : Ψ₀′ ⊑ᵘ Ψ′) {γ′ γ}
                → ThinAgree c Ψ′ Ψ γ′ γ → ThinAgree c Ψ₀′ Ψ (restrict σ P γ′) γ
  thinRestrictˡ cdone {Ψ = []} [] a = tt
  thinRestrictˡ (ckeep c) {Ψ = Zero ∷ Ψ} (0≤q ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , tt
  thinRestrictˡ (ckeep c) {Ψ = One ∷ Ψ} (0≤q ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , tt
  thinRestrictˡ (ckeep c) {Ψ = Many ∷ Ψ} (0≤q ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , tt
  thinRestrictˡ (ckeep c) {Ψ = Zero ∷ Ψ} (1≤1 ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , tt
  thinRestrictˡ (ckeep c) {Ψ = One ∷ Ψ} (1≤1 ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , sv
  thinRestrictˡ (ckeep c) {Ψ = Many ∷ Ψ} (1≤1 ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , sv
  thinRestrictˡ (ckeep c) {Ψ = Zero ∷ Ψ} (1≤ω ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , tt
  thinRestrictˡ (ckeep c) {Ψ = One ∷ Ψ} (1≤ω ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , sv
  thinRestrictˡ (ckeep c) {Ψ = Many ∷ Ψ} (1≤ω ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , sv
  thinRestrictˡ (ckeep c) {Ψ = Zero ∷ Ψ} (ω≤ω ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , tt
  thinRestrictˡ (ckeep c) {Ψ = One ∷ Ψ} (ω≤ω ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , sv
  thinRestrictˡ (ckeep c) {Ψ = Many ∷ Ψ} (ω≤ω ⊑∷ P) {γ′ , v′} {γ , v} (a , sv) = thinRestrictˡ c P a , sv
  thinRestrictˡ (cskip c) (0≤q ⊑∷ P) {γ′ , v′} a = thinRestrictˡ c P a
  thinRestrictˡ (cskip c) (1≤1 ⊑∷ P) {γ′ , v′} a = thinRestrictˡ c P a
  thinRestrictˡ (cskip c) (1≤ω ⊑∷ P) {γ′ , v′} a = thinRestrictˡ c P a
  thinRestrictˡ (cskip c) (ω≤ω ⊑∷ P) {γ′ , v′} a = thinRestrictˡ c P a

  thinRestrictʳ : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} (c : CThin θ Γ Γ′) {Ψ′ : Usage n′} {Ψ₀ Ψ : Usage n} (p : Ψ₀ ⊑ᵘ Ψ) {γ′ γ}
                → ThinAgree c Ψ′ Ψ γ′ γ → ThinAgree c Ψ′ Ψ₀ γ′ (restrict σ p γ)
  thinRestrictʳ cdone {Ψ′ = []} [] a = tt
  thinRestrictʳ (ckeep c) {Ψ′ = Zero ∷ Ψ′} (0≤q ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , tt
  thinRestrictʳ (ckeep c) {Ψ′ = One ∷ Ψ′} (0≤q ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , tt
  thinRestrictʳ (ckeep c) {Ψ′ = Many ∷ Ψ′} (0≤q ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , tt
  thinRestrictʳ (ckeep c) {Ψ′ = Zero ∷ Ψ′} (1≤1 ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , tt
  thinRestrictʳ (ckeep c) {Ψ′ = One ∷ Ψ′} (1≤1 ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , sv
  thinRestrictʳ (ckeep c) {Ψ′ = Many ∷ Ψ′} (1≤1 ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , sv
  thinRestrictʳ (ckeep c) {Ψ′ = Zero ∷ Ψ′} (1≤ω ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , tt
  thinRestrictʳ (ckeep c) {Ψ′ = One ∷ Ψ′} (1≤ω ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , sv
  thinRestrictʳ (ckeep c) {Ψ′ = Many ∷ Ψ′} (1≤ω ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , sv
  thinRestrictʳ (ckeep c) {Ψ′ = Zero ∷ Ψ′} (ω≤ω ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , tt
  thinRestrictʳ (ckeep c) {Ψ′ = One ∷ Ψ′} (ω≤ω ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , sv
  thinRestrictʳ (ckeep c) {Ψ′ = Many ∷ Ψ′} (ω≤ω ⊑∷ p) {γ′ , v′} {γ , v} (a , sv) = thinRestrictʳ c p a , sv
  thinRestrictʳ (cskip c) {Ψ′ = q′ ∷ Ψ′} p {γ′ , v′} a = thinRestrictʳ c p a

  thinLookup : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} (c : CThin θ Γ Γ′) (i : Fin n) {γ′ γ}
             → ThinAgree c (singleUse (⟦ θ ⟧θ i) One) (singleUse i One) γ′ γ
             → Same (lookup Γ i ⟨ σ ⟩) (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (cthin-lookup c i) (lookupᵛ σ Γ′ (⟦ θ ⟧θ i) γ′))
                                      (lookupᵛ σ Γ i γ)
  thinLookup (ckeep c) zero    {γ′ , v′} {γ , v} (a , sv) = sv
  thinLookup (ckeep c) (suc i) {γ′ , v′} {γ , v} (a , _)  = thinLookup c i a
  thinLookup (cskip c) i       {γ′ , v′}         a        = thinLookup c i a

retypeSem : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t A A′ π} (e : A ≡ A′) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
            (δ : DefSem) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) (γ : Env σ Γ Ψ)
          → ⟦ retype e d ⟧ δ σ r γ ≡ subst (λ X → M π ⟦ X ⟨ σ ⟩ ⟧ᵛ) e (⟦ d ⟧ δ σ r γ)
retypeSem refl d δ σ r γ = refl

------------------------------------------------------------------------
-- The lemma
------------------------------------------------------------------------

module RenSem {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where

  renSem : ∀ {n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) (h : ∀ i → ⟦ θ ⟧θ i ≡ ρ i) {Γ Γ′} (c : CThin θ Γ Γ′)
         → ∀ {Ψ t A π} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) {γ′ γ}
         → ThinAgree σ c (θ θ* Ψ) Ψ γ′ γ
         → Rel π π (A ⟨ σ ⟩) (⟦ ren-⊢ θ ρ h c d ⟧ δ σ r γ′) (⟦ d ⟧ δ σ r γ)

  private
    -- forgetting variables, on the renamed side twice (the rule's and the
    -- usage cast's) and on the original side once
    r3 : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} (c : CThin θ Γ Γ′) {Ψ₀′ Ψ₁′ Ψ′ Ψ₀ Ψ} (P : Ψ₀′ ⊑ᵘ Ψ₁′) (Q : Ψ₁′ ⊑ᵘ Ψ′) (p : Ψ₀ ⊑ᵘ Ψ) {γ′ γ}
       → ThinAgree σ c Ψ′ Ψ γ′ γ → ThinAgree σ c Ψ₀′ Ψ₀ (restrict σ P (restrict σ Q γ′)) (restrict σ p γ)
    r3 c P Q p ag = thinRestrictʳ σ c p (thinRestrictˡ σ c P (thinRestrictˡ σ c Q ag))

    varSem : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} (c : CThin θ Γ Γ′) (i : Fin n) {j} (e : ⟦ θ ⟧θ i ≡ j) {γ′ γ}
           → ThinAgree σ c (θ θ* singleUse i One) (singleUse i One) γ′ γ
           → Rel pure pure (lookup Γ i ⟨ σ ⟩) (⟦ varAt c i e ⟧ δ σ r γ′) (lookupᵛ σ Γ i γ)
    varSem {θ = θ} {Γ} {Γ′} c i refl {γ′} ag =
      relPure (subst (λ w → Same (lookup Γ i ⟨ σ ⟩) w _)
                     (sym (retypeSem (cthin-lookup c i) (⊢var (⟦ θ ⟧θ i)) δ σ r (restrict σ _ γ′)))
                     (thinLookup σ c i (thinRestrictˡ σ c _ ag)))

  renSem θ ρ h c (⊢var i) ag = varSem c i (h i) ag
  -- λ: the same arrow, its body one variable further
  renSem θ ρ h c (⊢lam {q = Zero} {π = π} {A} {B} 0≤q d) ag =
    relPure {A = (A ⇒[ mk-kind Zero π ] B) ⟨ σ ⟩} (lamZero {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩}
      (renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d (ag , tt)))
  renSem θ ρ h c (⊢lam {q = One} {π = π} {A} {B} 0≤q d) ag =
    relPure {A = (A ⇒[ mk-kind One π ] B) ⟨ σ ⟩} (lamOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa →
      renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d (ag , tt))
  renSem θ ρ h c (⊢lam {q = Many} {π = π} {A} {B} 0≤q d) ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa →
      renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d (ag , tt))
  renSem θ ρ h c (⊢lam {π = π} {A} {B} 1≤1 d) ag =
    relPure {A = (A ⇒[ mk-kind One π ] B) ⟨ σ ⟩} (lamOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa →
      renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d (ag , sa))
  renSem θ ρ h c (⊢lam {π = π} {A} {B} 1≤ω d) ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa →
      renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d (ag , sa))
  renSem θ ρ h c (⊢lam {π = π} {A} {B} ω≤ω d) ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa →
      renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d (ag , sa))
  -- application, by the arrow's quantity
  renSem θ ρ h c (⊢app {q = Zero} {A = A} df dx) ag =
    relBindᵍ (renSem θ ρ h c df (r3 c _ _ _ ag)) (appZero {A = A ⟨ σ ⟩})
  renSem θ ρ h c (⊢app {q = One} df dx) ag =
    relBindᵍ (renSem θ ρ h c df (r3 c _ _ _ ag)) λ sf →
    relBindᵍ (renSem θ ρ h c dx (r3 c _ _ _ ag)) λ sx → appOne sf sx
  renSem θ ρ h c (⊢app {q = Many} df dx) ag =
    relBindᵍ (renSem θ ρ h c df (r3 c _ _ _ ag)) λ sf →
    relBindᵍ (renSem θ ρ h c dx (r3 c _ _ _ ag)) λ sx → appMany sf sx
  -- let, by the binder's quantity
  renSem θ ρ h c (⊢let {q = Zero} d₁ d₂) ag =
    renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d₂ (r3 c _ _ _ ag , tt)
  renSem θ ρ h c (⊢let {q = One} d₁ d₂) ag =
    relBindᵍ (renSem θ ρ h c d₁ (r3 c _ _ _ ag)) λ sv →
    renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d₂ (r3 c _ _ _ ag , sv)
  renSem θ ρ h c (⊢let {q = Many} d₁ d₂) ag =
    relBindᵍ (renSem θ ρ h c d₁ (r3 c _ _ _ ag)) λ sv →
    renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) d₂ (r3 c _ _ _ ag , sv)
  renSem θ ρ h c ⊢unit ag = relPure tt
  renSem θ ρ h c (⊢pair {π₁ = π₁} {π₂} {A} {B} da db) ag =
    relBindᵍ {π₁} {π₂} {π₁} {π₂} {A ⟨ σ ⟩} {(A * B) ⟨ σ ⟩} (renSem θ ρ h c da (r3 c _ _ _ ag)) λ sa →
    relFmap {π₂} {π₂} {B ⟨ σ ⟩} {(A * B) ⟨ σ ⟩} (renSem θ ρ h c db (r3 c _ _ _ ag)) λ sb → samePair {A ⟨ σ ⟩} {B ⟨ σ ⟩} sa sb
  renSem θ ρ h c (⊢fst {A = A} {B} d) ag = relFmap (renSem θ ρ h c d ag) (sameFst {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩})
  renSem θ ρ h c (⊢snd {A = A} {B} d) ag = relFmap (renSem θ ρ h c d ag) (sameSnd {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩})
  renSem θ ρ h c (⊢inl {π = π} {A} {B} d) ag = relFmap {π} {π} (renSem θ ρ h c d ag) (sameInl {A ⟨ σ ⟩} {B ⟨ σ ⟩})
  renSem θ ρ h c (⊢inr {π = π} {A} {B} d) ag = relFmap {π} {π} (renSem θ ρ h c d ag) (sameInr {A ⟨ σ ⟩} {B ⟨ σ ⟩})
  renSem θ ρ h c (⊢case {qℓ = qℓ} {qr} {π₁} {π₂} {A} {B} {C} ds dl dr) ag =
    relBindᵍ (renSem θ ρ h c ds (r3 c _ _ _ ag)) λ {w} {w′} sw →
      caseRel {A ⟨ σ ⟩} {B ⟨ σ ⟩} {C ⟨ σ ⟩} {π₂} {π₂}
        (λ {a} {a′} sa → renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) dl (r3 c _ _ _ ag , slotSame σ A qℓ {a} {a′} sa))
        (λ {b} {b′} sb → renSem (keep θ) _ (ext-hρ {m = m} θ ρ h) (ckeep c) dr (r3 c _ _ _ ag , slotSame σ B qr {b} {b′} sb))
        {w} {w′} sw
  renSem θ ρ h c (⊢absurd {π = π} d) ag = relBind {π} {π} (renSem θ ρ h c d ag) λ {x} _ → ⊥-elim x
  renSem θ ρ h c (⊢roll {π = π} wf d) ag = relFmap {π} {π} (renSem θ ρ h c d ag) λ s → Functor.roll-same σ r wf s
  renSem θ ρ h c (⊢fold {π = π} {F = F} {A} wf da dt) ag =
    relBindᵍ (renSem θ ρ h c da (r3 c _ _ _ ag)) λ {alg} {alg′} salg →
    relBindᵍ (renSem θ ρ h c dt (r3 c _ _ _ ag)) λ {v} {v′} sv →
    subst (λ w → Rel π π (A ⟨ σ ⟩) (foldM π (code (F ⟨ σ ⟩F)) (λ l → alg (fromL σ F A l)) v)
                                     (foldM π (code (F ⟨ σ ⟩F)) (λ l → alg′ (fromL σ F A l)) w))
          (sameμ sv)
          (Fold.foldRel π (code (F ⟨ σ ⟩F)) (A ⟨ σ ⟩) _ _ (λ le → appMany salg (Functor.fromL-same σ r wf A le)) v)
  renSem θ ρ h c (⊢unfold {f = f} {F = F} {A} wf dc da) ag =
    relBindᵍ (renSem θ ρ h c dc (r3 c _ _ _ ag)) λ {c₁} {c₂} sc →
    relFmap (renSem θ ρ h c da (r3 c _ _ _ ag)) λ sa n →
      Ana.anaRel f (code (F ⟨ σ ⟩F)) (A ⟨ σ ⟩) (λ x → fmap (fin f) (toL σ F A) (c₁ x)) (λ x → fmap (fin f) (toL σ F A) (c₂ x))
        (λ {a} {a′} s → ≈-Relatedˡ (toT∞-fmap (fin f) (toL σ F A) (c₁ a)) (≈-Relatedʳ (toT∞-fmap (fin f) (toL σ F A) (c₂ a′))
                          (relatedFmap (runs (appMany {π = fin f} sc s)) (Functor.toL-same σ r wf A))))
        n sa
  renSem θ ρ h c (⊢out {f = f} {F = F} wf d) ag =
    relBindᵍ (renSem θ ρ h c d ag) λ {v} {v′} sv → rel (
      ≈-Relatedˡ (toT∞-fmap (fin f) (fromL σ F (ν F f)) (outν v))
        (≈-Relatedʳ (toT∞-fmap (fin f) (fromL σ F (ν F f)) (outν v′))
          (relatedFmap (outRel f (code (F ⟨ σ ⟩F)) sv)
                    (λ k → Functor.fromL-same σ r wf (ν F f) (LayerEq-∀ (code (F ⟨ σ ⟩F)) k)))))
  renSem θ ρ h c (⊢iter {A = A} {B} df ds) ag =
    relBindᵍ (renSem θ ρ h c df (r3 c _ _ _ ag)) λ {f} {f′} sf →
    relBindᵍ (renSem θ ρ h c ds (r3 c _ _ _ ag)) λ sa →
    rel (loopSame (A ⟨ σ ⟩) (B ⟨ σ ⟩) f f′ (λ s → runs (appMany {π = act} sf s)) sa)
  renSem θ ρ h c (⊢coerce p d) ag = relFmap (renSem θ ρ h c d ag) (convSame σ p)
  renSem θ ρ h c ⊢lit-int ag = relPure {A = Int} refl
  renSem θ ρ h c ⊢lit-float ag = relPure {A = Float} refl
  renSem θ ρ h c (⊢prim {π = π} p d) ag = relFmap {π} {π} (renSem θ ρ h c d ag) (primSame σ p)
  renSem θ ρ h c (⊢sigop {c = c₀} {t} mem) ag = relPure (sigopRefl σ c₀ t mem (model δ))
  renSem θ ρ h c (⊢ref d τ rd) ag =
    relPure (substSame (sym (⟨⟩-∘ (type (S !! d)) τ σ))
                       (sd d (λ i → τ i ⟨ σ ⟩) (respects-∘ rd r) (respects-∘ rd r)))
  renSem θ ρ h c (⊢sub-use p d) ag = renSem θ ρ h c d (thinRestrictʳ σ c p (thinRestrictˡ σ c (θ*-mono θ p) ag))
  renSem θ ρ h c (⊢sub-eff g d) ag = relSubˡ g (relSubʳ g (renSem θ ρ h c d ag))
