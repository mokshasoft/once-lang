{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Abstraction — the abstraction theorem: two
-- derivations of one core term, at two instances of the type variables with
-- a relation for each, in environments related by their types, mean
-- computations related by the relational reading of the type
-- (`Spec.Metatheory.Parametricity.abstraction`).
--
-- The fundamental lemma of `Coherence.Fundamental`, read between two
-- instances: by induction on the two derivations, each former's case the
-- congruence of its semantic operation for the relational reading
-- (`Parametricity.Comp`, `Parametricity.Values`). No case looks at a type
-- variable: a variable's values are only passed along, and the one place an
-- instance enters a meaning, a reference to a definition, is related by the
-- hypothesis on the definitions (`ParamDefs`) at the composed instances,
-- read back through substitution (`Parametricity.Subst`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName; _∶_; ⌜_⌝ᵈ)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Parametricity.Abstraction (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Once.Spec.Grade using (fin; Zero; One; Many; Purity; pure; act; eff; mk-kind; 0≤q; 1≤1; 1≤ω; ω≤ω; positionGrade; _·p_)
open import Once.Spec.Type
  using (Ty; KCtx; ∅ₖ; TySub; Respects; WFFun; _⟨_⟩; _⟨_⟩F; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F)
open import Once.Spec.Context using (Ctx; _▸_; Usage; _∷_; _⊑ᵘ_; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Type.Substitution using (respects-∘)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; toT∞; fmap; module νM)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM)
open import Once.Spec.Equivalence Σ using (Rel; RelF; RelSub; RelMu; inR)
open import Once.Spec.Metatheory using (ParamDefs; RelEnv)
open import Once.Spec.Sub using (_<:_)
open import Once.Metatheory.Types using (<:-unique)
open import Once.Metatheory.Erase Σ using (toT∞-fmap)
open import Once.Metatheory.Coherence.Relation Σ using (Related-mono; ≈-Relatedˡ; ≈-Relatedʳ; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (relatedFmap)
open import Once.Metatheory.Coherence.Loop Σ using (loopRel; SumR)
open import Once.Metatheory.Coherence.Sigop Σ using (module Names)
open import Once.Metatheory.Coherence.Env Σ fmt S
  using (envˡ-restrict; envʳ-restrict; env*One-envʳ-restrict; env*Many-envʳ-restrict; env*Many-envˡ-restrict)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Parametricity.Comp Σ
open import Once.Metatheory.Parametricity.Env Σ fmt S
open import Once.Metatheory.Parametricity.Values Σ
open import Once.Metatheory.Parametricity.Subst Σ using (rel-sub→; ρ∘τ)
open Names u

open DefSem

module AL {m : ℕ} {Δ : KCtx m} (δ : DefSem) (pd : ParamDefs Σ fmt S δ)
          {σ σ′ : TySub m 0} (r : Respects Δ ∅ₖ σ) (r′ : Respects Δ ∅ₖ σ′) (ρ : RelSub σ σ′) where

  -- The second meaning, read at the first derivation's type.
  substM : ∀ π {A A′ : Ty m} → A′ ≡ A → M π ⟦ A′ ⟨ σ′ ⟩ ⟧ᵛ → M π ⟦ A ⟨ σ′ ⟩ ⟧ᵛ
  substM π refl x = x

  AL : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ t A A′ π π′} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A′ ! π′)
       (eq : A′ ≡ A) {γ γ′} → RAgree ρ Γ Ψ Ψ′ γ γ′
     → RC π π′ (Rel A ρ) (⟦ d ⟧ δ σ r γ) (substM π′ eq (⟦ d′ ⟧ δ σ′ r′ γ′))

  private
    rr : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ Ψ₀′ Ψ′ : Usage n} (p : Ψ₀ ⊑ᵘ Ψ) (p′ : Ψ₀′ ⊑ᵘ Ψ′) {γ γ′}
       → RAgree ρ Γ Ψ Ψ′ γ γ′ → RAgree ρ Γ Ψ₀ Ψ₀′ (restrict σ p γ) (restrict σ′ p′ γ′)
    rr p p′ ag = rrestrictˡ ρ p (rrestrictʳ ρ p′ ag)

    rr≡ : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ Ψ₀′ Ψ′ : Usage n} {p : Ψ₀ ⊑ᵘ Ψ} {p′ : Ψ₀′ ⊑ᵘ Ψ′} {γ γ′ γ₀ γ₀′}
        → γ₀ ≡ restrict σ p γ → γ₀′ ≡ restrict σ′ p′ γ′
        → RAgree ρ Γ Ψ Ψ′ γ γ′ → RAgree ρ Γ Ψ₀ Ψ₀′ γ₀ γ₀′
    rr≡ {p = p} {p′} refl refl ag = rr p p′ ag

    -- Branching on related sums.
    caseR : ∀ {A B C : Ty m} {π π′} {l l′ k k′}
          → (∀ {a a′} → Rel A ρ a a′ → RC π π′ (Rel C ρ) (l a) (l′ a′))
          → (∀ {b b′} → Rel B ρ b b′ → RC π π′ (Rel C ρ) (k b) (k′ b′))
          → ∀ {w w′} → Rel (A + B) ρ w w′ → RC π π′ (Rel C ρ) ([ l , k ]′ w) ([ l′ , k′ ]′ w′)
    caseR hl hr {inj₁ a} {inj₁ a′} s = hl s
    caseR hl hr {inj₂ b} {inj₂ b′} s = hr s
    caseR hl hr {inj₁ a} {inj₂ b′} ()
    caseR hl hr {inj₂ b} {inj₁ a′} ()

    -- A round's result, read as the loop's.
    split : ∀ {A B : Ty m} {x y} → Rel (B + A) ρ x y → SumR (Rel B ρ) (Rel A ρ) x y
    split {x = inj₁ _} {inj₁ _} p = p
    split {x = inj₂ _} {inj₂ _} p = p
    split {x = inj₁ _} {inj₂ _} ()
    split {x = inj₂ _} {inj₁ _} ()

  -- application, at one arrow type
  appH : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ Ψ₁′ Ψ₂′ q q′ π π″ π₁ π₂ π₁′ π₂′ A₁ A₂ B f x}
       → (A₁ ⇒[ mk-kind q π ] B) ≡ (A₂ ⇒[ mk-kind q′ π″ ] B)
       → (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A₁ ⇒[ mk-kind q π ] B ! π₁) (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A₁ ! positionGrade q π₂)
       → (df′ : Δ ⊩ Γ ⊢[ Ψ₁′ ] f ∷ A₂ ⇒[ mk-kind q′ π″ ] B ! π₁′) (dx′ : Δ ⊩ Γ ⊢[ Ψ₂′ ] x ∷ A₂ ! positionGrade q′ π₂′)
       → ∀ {γ γ′} → RAgree ρ Γ (Ψ₁ +ᵘ q *ᵘ Ψ₂) (Ψ₁′ +ᵘ q′ *ᵘ Ψ₂′) γ γ′
       → RC _ _ (Rel B ρ) (⟦ ⊢app df dx ⟧ δ σ r γ) (⟦ ⊢app df′ dx′ ⟧ δ σ′ r′ γ′)
  appH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = Zero} {π = π} refl df dx df′ dx′ ag =
    rcBindᵍ (AL df df′ refl (rr≡ (envˡ-restrict σ Ψ₁ (Zero *ᵘ Ψ₂) _) (envˡ-restrict σ′ Ψ₁′ (Zero *ᵘ Ψ₂′) _) ag)) λ sf → rcObs π π sf
  appH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = One} {π = π} refl df dx df′ dx′ ag =
    rcBindᵍ (AL df df′ refl (rr≡ (envˡ-restrict σ Ψ₁ (One *ᵘ Ψ₂) _) (envˡ-restrict σ′ Ψ₁′ (One *ᵘ Ψ₂′) _) ag)) λ sf →
    rcBindᵍ (AL dx dx′ refl (rr≡ (env*One-envʳ-restrict σ Ψ₁ Ψ₂ _) (env*One-envʳ-restrict σ′ Ψ₁′ Ψ₂′ _) ag)) λ sx → rcObs π π (sf _ _ sx)
  appH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = Many} {π = π} refl df dx df′ dx′ ag =
    rcBindᵍ (AL df df′ refl (rr≡ (envˡ-restrict σ Ψ₁ (Many *ᵘ Ψ₂) _) (envˡ-restrict σ′ Ψ₁′ (Many *ᵘ Ψ₂′) _) ag)) λ sf →
    rcBindᵍ (AL dx dx′ refl (rr≡ (env*Many-envʳ-restrict σ Ψ₁ Ψ₂ _) (env*Many-envʳ-restrict σ′ Ψ₁′ Ψ₂′ _) ag)) λ sx → rcObs π π (sf _ _ sx)

  letH : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ Ψ₁′ Ψ₂′ q π₁ π₂ π₁′ π₂′ A A′ B e b}
       → A ≡ A′
       → (d₁ : Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁) (d₂ : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂)
       → (d₁′ : Δ ⊩ Γ ⊢[ Ψ₁′ ] e ∷ A′ ! positionGrade q π₁′) (d₂′ : Δ ⊩ (Γ ▸ A′) ⊢[ q ∷ Ψ₂′ ] b ∷ B ! π₂′)
       → ∀ {γ γ′} → RAgree ρ Γ (Ψ₂ +ᵘ q *ᵘ Ψ₁) (Ψ₂′ +ᵘ q *ᵘ Ψ₁′) γ γ′
       → RC _ _ (Rel B ρ) (⟦ ⊢let d₁ d₂ ⟧ δ σ r γ) (⟦ ⊢let d₁′ d₂′ ⟧ δ σ′ r′ γ′)
  letH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = Zero} refl d₁ d₂ d₁′ d₂′ ag =
    AL d₂ d₂′ refl (rr≡ (envˡ-restrict σ Ψ₂ (Zero *ᵘ Ψ₁) _) (envˡ-restrict σ′ Ψ₂′ (Zero *ᵘ Ψ₁′) _) ag , tt)
  letH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = One} refl d₁ d₂ d₁′ d₂′ ag =
    rcBindᵍ (AL d₁ d₁′ refl (rr≡ (env*One-envʳ-restrict σ Ψ₂ Ψ₁ _) (env*One-envʳ-restrict σ′ Ψ₂′ Ψ₁′ _) ag)) λ sv →
    AL d₂ d₂′ refl (rr≡ (envˡ-restrict σ Ψ₂ (One *ᵘ Ψ₁) _) (envˡ-restrict σ′ Ψ₂′ (One *ᵘ Ψ₁′) _) ag , sv)
  letH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = Many} refl d₁ d₂ d₁′ d₂′ ag =
    rcBindᵍ (AL d₁ d₁′ refl (rr≡ (env*Many-envʳ-restrict σ Ψ₂ Ψ₁ _) (env*Many-envʳ-restrict σ′ Ψ₂′ Ψ₁′ _) ag)) λ sv →
    AL d₂ d₂′ refl (rr≡ (envˡ-restrict σ Ψ₂ (Many *ᵘ Ψ₁) _) (envˡ-restrict σ′ Ψ₂′ (Many *ᵘ Ψ₁′) _) ag , sv)

  fstH : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ π π′ A B B′ p}
       → (A * B) ≡ (A * B′) → (d : Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] p ∷ A * B′ ! π′)
       → ∀ {γ γ′} → RAgree ρ Γ Ψ Ψ′ γ γ′ → RC π π′ (Rel A ρ) (⟦ ⊢fst d ⟧ δ σ r γ) (⟦ ⊢fst d′ ⟧ δ σ′ r′ γ′)
  fstH refl d d′ ag = rcFmap (AL d d′ refl ag) proj₁

  sndH : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ π π′ A A′ B p}
       → (A * B) ≡ (A′ * B) → (d : Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] p ∷ A′ * B ! π′)
       → ∀ {γ γ′} → RAgree ρ Γ Ψ Ψ′ γ γ′ → RC π π′ (Rel B ρ) (⟦ ⊢snd d ⟧ δ σ r γ) (⟦ ⊢snd d′ ⟧ δ σ′ r′ γ′)
  sndH refl d d′ ag = rcFmap (AL d d′ refl ag) proj₂

  caseH : ∀ {n} {Γ : Ctx m n} {Ψs Ψ Ψs′ Ψ′ qℓ qr π₁ π₂ π₁′ π₂′ A B A′ B′ C e l rt}
        → (A + B) ≡ (A′ + B′)
        → (ds : Δ ⊩ Γ ⊢[ Ψs ] e ∷ A + B ! π₁) (dl : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π₂) (dr : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψ ] rt ∷ C ! π₂)
        → (ds′ : Δ ⊩ Γ ⊢[ Ψs′ ] e ∷ A′ + B′ ! π₁′) (dl′ : Δ ⊩ (Γ ▸ A′) ⊢[ qℓ ∷ Ψ′ ] l ∷ C ! π₂′)
          (dr′ : Δ ⊩ (Γ ▸ B′) ⊢[ qr ∷ Ψ′ ] rt ∷ C ! π₂′)
        → ∀ {γ γ′} → RAgree ρ Γ (Ψs +ᵘ Ψ) (Ψs′ +ᵘ Ψ′) γ γ′
        → RC _ _ (Rel C ρ) (⟦ ⊢case ds dl dr ⟧ δ σ r γ) (⟦ ⊢case ds′ dl′ dr′ ⟧ δ σ′ r′ γ′)
  caseH {Ψs = Ψs} {Ψ} {Ψs′} {Ψ′} {qℓ} {qr} {A = A} {B} {C = C} refl ds dl dr ds′ dl′ dr′ ag =
    rcBindᵍ (AL ds ds′ refl (rr≡ (envˡ-restrict σ Ψs Ψ _) (envˡ-restrict σ′ Ψs′ Ψ′ _) ag))
      (λ {w} {w′} sw → caseR {A} {B} {C}
               (λ {a} {a′} sa → AL dl dl′ refl (rr≡ (envʳ-restrict σ Ψs Ψ _) (envʳ-restrict σ′ Ψs′ Ψ′ _) ag , rslot ρ A qℓ {a} {a′} sa))
               (λ {b} {b′} sb → AL dr dr′ refl (rr≡ (envʳ-restrict σ Ψs Ψ _) (envʳ-restrict σ′ Ψs′ Ψ′ _) ag , rslot ρ B qr {b} {b′} sb))
               {w} {w′} sw)

  foldH : ∀ {n} {Γ : Ctx m n} {Ψa Ψt Ψa′ Ψt′ π π′ π₁ π₂ π₁′ π₂′ F A alg t}
        → (⟦ F ⟧F A ⇒[ mk-kind Many π ] A) ≡ (⟦ F ⟧F A ⇒[ mk-kind Many π′ ] A)
        → (wf : WFFun Δ F) (da : Δ ⊩ Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! π₁)
          (dt : Δ ⊩ Γ ⊢[ Ψt ] t ∷ μ F ! π₂)
        → (wf′ : WFFun Δ F) (da′ : Δ ⊩ Γ ⊢[ Ψa′ ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π′ ] A ! π₁′)
          (dt′ : Δ ⊩ Γ ⊢[ Ψt′ ] t ∷ μ F ! π₂′)
        → ∀ {γ γ′} → RAgree ρ Γ (Many *ᵘ Ψa +ᵘ Ψt) (Many *ᵘ Ψa′ +ᵘ Ψt′) γ γ′
        → RC _ _ (Rel A ρ) (⟦ ⊢fold wf da dt ⟧ δ σ r γ) (⟦ ⊢fold wf′ da′ dt′ ⟧ δ σ′ r′ γ′)
  foldH {Ψa = Ψa} {Ψt} {Ψa′} {Ψt′} {π} {F = F} {A} refl wf da dt wf′ da′ dt′ ag =
    rcBindᵍ (AL da da′ refl (rr≡ (env*Many-envˡ-restrict σ Ψa Ψt _) (env*Many-envˡ-restrict σ′ Ψa′ Ψt′ _) ag)) λ {alg} {alg′} salg →
    rcBindᵍ (AL dt dt′ refl (rr≡ (envʳ-restrict σ (Many *ᵘ Ψa) Ψt _) (envʳ-restrict σ′ (Many *ᵘ Ψa′) Ψt′ _) ag)) λ {v} {v′} sv →
    FoldR.foldRel π (RelF F ρ) (Rel A ρ) (λ l → alg (fromL σ F A l)) (λ l → alg′ (fromL σ′ F A l))
      (λ le → rcObs π π (salg _ _ (fromL-rel ρ F A le))) sv

  unfoldH : ∀ {n} {Γ : Ctx m n} {Ψc Ψs Ψc′ Ψs′ f π₁ π₂ π₁′ π₂′ F A A′ c a}
          → (A ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A) ≡ (A′ ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A′)
          → (wf : WFFun Δ F) (dc : Δ ⊩ Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A ! π₁) (da : Δ ⊩ Γ ⊢[ Ψs ] a ∷ A ! π₂)
          → (wf′ : WFFun Δ F) (dc′ : Δ ⊩ Γ ⊢[ Ψc′ ] c ∷ A′ ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A′ ! π₁′)
            (da′ : Δ ⊩ Γ ⊢[ Ψs′ ] a ∷ A′ ! π₂′)
          → ∀ {γ γ′} → RAgree ρ Γ (Many *ᵘ Ψc +ᵘ Ψs) (Many *ᵘ Ψc′ +ᵘ Ψs′) γ γ′
          → RC _ _ (Rel (ν F f) ρ) (⟦ ⊢unfold wf dc da ⟧ δ σ r γ) (⟦ ⊢unfold wf′ dc′ da′ ⟧ δ σ′ r′ γ′)
  unfoldH {Ψc = Ψc} {Ψs} {Ψc′} {Ψs′} {f} {F = F} {A} refl wf dc da wf′ dc′ da′ ag =
    rcBindᵍ (AL dc dc′ refl (rr≡ (env*Many-envˡ-restrict σ Ψc Ψs _) (env*Many-envˡ-restrict σ′ Ψc′ Ψs′ _) ag)) λ {c} {c′} sc →
    rcFmap (AL da da′ refl (rr≡ (envʳ-restrict σ (Many *ᵘ Ψc) Ψs _) (envʳ-restrict σ′ (Many *ᵘ Ψc′) Ψs′ _) ag)) λ sa n →
      AnaR.anaRel f (RelF F ρ) (Rel A ρ) (λ x → fmap (fin f) (toL σ F A) (c x)) (λ x → fmap (fin f) (toL σ′ F A) (c′ x))
        (λ {a} {a′} s → ≈-Relatedˡ (toT∞-fmap (fin f) (toL σ F A) (c a)) (≈-Relatedʳ (toT∞-fmap (fin f) (toL σ′ F A) (c′ a′))
                          (relatedFmap (fromObserved (sc _ _ s)) (toL-rel ρ F A))))
        n sa

  outH : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ f f′ π₁ π₁′ F F′ t}
       → ν F f ≡ ν F′ f′ → (eq : ⟦ F′ ⟧F (ν F′ f′) ≡ ⟦ F ⟧F (ν F f))
       → (wf : WFFun Δ F) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ ν F f ! π₁) (wf′ : WFFun Δ F′) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ ν F′ f′ ! π₁′)
       → ∀ {γ γ′} → RAgree ρ Γ Ψ Ψ′ γ γ′
       → RC _ _ (Rel (⟦ F ⟧F (ν F f)) ρ) (⟦ ⊢out wf d ⟧ δ σ r γ) (substM (π₁′ ·p fin f′) eq (⟦ ⊢out wf′ d′ ⟧ δ σ′ r′ γ′))
  outH {f = f} {F = F} refl refl wf d wf′ d′ ag =
    rcBindᵍ (AL d d′ refl ag) λ {v} {v′} sv → rc (
      ≈-Relatedˡ (toT∞-fmap (fin f) (fromL σ F (ν F f)) (outν v))
        (≈-Relatedʳ (toT∞-fmap (fin f) (fromL σ′ F (ν F f)) (outν v′))
          (relatedFmap (outRelR f (RelF F ρ) sv) (fromL-rel ρ F (ν F f)))))

  iterH : ∀ {n} {Γ : Ctx m n} {Ψf Ψs Ψf′ Ψs′ π₁ π₂ π₁′ π₂′ A A′ B f a}
        → (A ⇒[ mk-kind Many act ] (B + A)) ≡ (A′ ⇒[ mk-kind Many act ] (B + A′))
        → (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind Many act ] (B + A) ! π₁) (ds : Δ ⊩ Γ ⊢[ Ψs ] a ∷ A ! π₂)
        → (df′ : Δ ⊩ Γ ⊢[ Ψf′ ] f ∷ A′ ⇒[ mk-kind Many act ] (B + A′) ! π₁′) (ds′ : Δ ⊩ Γ ⊢[ Ψs′ ] a ∷ A′ ! π₂′)
        → ∀ {γ γ′} → RAgree ρ Γ (Many *ᵘ Ψf +ᵘ Ψs) (Many *ᵘ Ψf′ +ᵘ Ψs′) γ γ′
        → RC _ _ (Rel B ρ) (⟦ ⊢iter df ds ⟧ δ σ r γ) (⟦ ⊢iter df′ ds′ ⟧ δ σ′ r′ γ′)
  iterH {Ψf = Ψf} {Ψs} {Ψf′} {Ψs′} {A = A} {B = B} refl df ds df′ ds′ ag =
    rcBindᵍ (AL df df′ refl (rr≡ (env*Many-envˡ-restrict σ Ψf Ψs _) (env*Many-envˡ-restrict σ′ Ψf′ Ψs′ _) ag)) λ {f} {f′} sf →
    rcBindᵍ (AL ds ds′ refl (rr≡ (envʳ-restrict σ (Many *ᵘ Ψf) Ψs _) (envʳ-restrict σ′ (Many *ᵘ Ψf′) Ψs′ _) ag)) λ sa →
    rc (loopRel (Rel A ρ) (Rel B ρ) f f′ (λ s → Related-mono (λ {x} {y} q → split {A} {B} {x} {y} q) (fromObserved (sf _ _ s))) sa)

  coerceH : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ π π′ A B t} (p p′ : A <: B)
          → (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A ! π′)
          → ∀ {γ γ′} → RAgree ρ Γ Ψ Ψ′ γ γ′
          → RC π π′ (Rel B ρ) (⟦ ⊢coerce p d ⟧ δ σ r γ) (⟦ ⊢coerce p′ d′ ⟧ δ σ′ r′ γ′)
  coerceH p p′ d d′ ag rewrite <:-unique p′ p = rcFmap (AL d d′ refl ag) (convRel ρ p)

  sigopH : ∀ {c t} (mem mem′ : (c ∶ t) ∈ Σ)
         → RC pure pure (Rel ⌜ t ⌝ᵈ ρ) (sigopᵛ σ c t mem (model δ)) (sigopᵛ σ′ c t mem′ (model δ))
  sigopH {c} {t} mem mem′ rewrite mem-unique mem′ mem = rcPure (sigopRel ρ {fmt} {s} {S} c t mem (model δ))

  -- Peeling the structural rules.
  AL (⊢sub-use p d) d′ eq ag = AL d d′ eq (rrestrictˡ ρ p ag)
  AL (⊢sub-eff g d) d′ eq ag = rcSubˡ g (AL d d′ eq ag)
  {-# CATCHALL #-}
  AL d (⊢sub-use p d′) refl ag = AL d d′ refl (rrestrictʳ ρ p ag)
  {-# CATCHALL #-}
  AL d (⊢sub-eff g d′) refl ag = rcSubʳ g (AL d d′ refl ag)
  -- One former, on both sides.
  AL (⊢var i) (⊢var .i) refl ag = rcPure (rlookup ρ _ i ag)
  AL (⊢lam {q = Zero} 0≤q d) (⊢lam 0≤q d′) refl ag = rcPure (obsRC (AL d d′ refl (ag , tt)))
  AL (⊢lam {q = One} 0≤q d) (⊢lam 0≤q d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , tt))
  AL (⊢lam {q = One} 0≤q d) (⊢lam 1≤1 d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , tt))
  AL (⊢lam {q = One} 1≤1 d) (⊢lam 0≤q d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , tt))
  AL (⊢lam {q = One} 1≤1 d) (⊢lam 1≤1 d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , sa))
  AL (⊢lam {q = Many} 0≤q d) (⊢lam 0≤q d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , tt))
  AL (⊢lam {q = Many} 0≤q d) (⊢lam 1≤ω d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , tt))
  AL (⊢lam {q = Many} 0≤q d) (⊢lam ω≤ω d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , tt))
  AL (⊢lam {q = Many} 1≤ω d) (⊢lam 0≤q d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , tt))
  AL (⊢lam {q = Many} 1≤ω d) (⊢lam 1≤ω d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , sa))
  AL (⊢lam {q = Many} 1≤ω d) (⊢lam ω≤ω d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , sa))
  AL (⊢lam {q = Many} ω≤ω d) (⊢lam 0≤q d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , tt))
  AL (⊢lam {q = Many} ω≤ω d) (⊢lam 1≤ω d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , sa))
  AL (⊢lam {q = Many} ω≤ω d) (⊢lam ω≤ω d′) refl ag = rcPure λ a a′ sa → obsRC (AL d d′ refl (ag , sa))
  AL (⊢app df dx) (⊢app df′ dx′) refl ag = appH (ty-unique df df′) df dx df′ dx′ ag
  AL (⊢let d₁ d₂) (⊢let d₁′ d₂′) refl ag = letH (ty-unique d₁ d₁′) d₁ d₂ d₁′ d₂′ ag
  AL ⊢unit ⊢unit refl ag = rcPure tt
  AL (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} da db) (⊢pair {Ψ₁ = Ψ₁′} {Ψ₂′} da′ db′) refl ag =
    rcBindᵍ (AL da da′ refl (rr≡ (envˡ-restrict σ Ψ₁ Ψ₂ _) (envˡ-restrict σ′ Ψ₁′ Ψ₂′ _) ag)) λ sa →
    rcFmap (AL db db′ refl (rr≡ (envʳ-restrict σ Ψ₁ Ψ₂ _) (envʳ-restrict σ′ Ψ₁′ Ψ₂′ _) ag)) λ sb → sa , sb
  AL (⊢fst d) (⊢fst d′) refl ag = fstH (ty-unique d d′) d d′ ag
  AL (⊢snd d) (⊢snd d′) refl ag = sndH (ty-unique d d′) d d′ ag
  AL (⊢inl d) (⊢inl d′) refl ag = rcFmap (AL d d′ refl ag) λ s → s
  AL (⊢inr d) (⊢inr d′) refl ag = rcFmap (AL d d′ refl ag) λ s → s
  AL (⊢case ds dl dr) (⊢case ds′ dl′ dr′) refl ag = caseH (ty-unique ds ds′) ds dl dr ds′ dl′ dr′ ag
  AL (⊢absurd d) (⊢absurd d′) refl ag = rcBind (AL d d′ refl ag) λ {x} _ → ⊥-elim x
  AL (⊢roll {F = F} wf d) (⊢roll wf′ d′) refl ag = rcFmap (AL d d′ refl ag) λ s → inR (toL-rel ρ F (μ F) s)
  AL (⊢fold wf da dt) (⊢fold wf′ da′ dt′) refl ag = foldH (ty-unique da da′) wf da dt wf′ da′ dt′ ag
  AL (⊢unfold wf dc da) (⊢unfold wf′ dc′ da′) refl ag = unfoldH (ty-unique dc dc′) wf dc da wf′ dc′ da′ ag
  AL (⊢out wf d) (⊢out wf′ d′) eq ag = outH (ty-unique d d′) eq wf d wf′ d′ ag
  AL (⊢iter df ds) (⊢iter df′ ds′) refl ag = iterH (ty-unique df df′) df ds df′ ds′ ag
  AL (⊢coerce p d) (⊢coerce p′ d′) refl ag = coerceH p p′ d d′ ag
  AL ⊢lit-int ⊢lit-int refl ag = rcPure refl
  AL ⊢lit-float ⊢lit-float refl ag = rcPure refl
  AL (⊢prim p d) (⊢prim .p d′) refl ag = rcFmap (AL d d′ refl ag) (primRel ρ {fmt} {s} {S} p)
  AL (⊢sigop mem) (⊢sigop mem′) refl ag = sigopH mem mem′
  AL (⊢ref d τ rd) (⊢ref .d .τ rd′) refl ag =
    rcPure (rel-sub→ τ ρ (type (S !! d))
              (pd d (λ i → τ i ⟨ σ ⟩) (λ i → τ i ⟨ σ′ ⟩) (respects-∘ rd r) (respects-∘ rd′ r′) (ρ∘τ τ ρ)))

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

abstraction : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t A π} (d d′ : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
                (δ : DefSem) → ParamDefs Σ fmt S δ
            → (σ σ′ : TySub m 0) (r : Respects Δ ∅ₖ σ) (r′ : Respects Δ ∅ₖ σ′) (ρ : RelSub σ σ′)
              (γ : Env σ Γ Ψ) (γ′ : Env σ′ Γ Ψ) → RelEnv Σ fmt S ρ Γ Ψ γ γ′
            → RC π π (Rel A ρ) (⟦ d ⟧ δ σ r γ) (⟦ d′ ⟧ δ σ′ r′ γ′)
abstraction {Γ = Γ} {Ψ} d d′ δ pd σ σ′ r r′ ρ γ γ′ e = AL.AL δ pd r r′ ρ d d′ refl (relAgree ρ Γ Ψ e)
