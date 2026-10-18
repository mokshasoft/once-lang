{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Fundamental — the fundamental lemma: two
-- derivations of one core term, in agreeing environments, mean related
-- computations (`Spec.Metatheory.Coherence`).
--
-- By induction on the two derivations. `⊢sub-use` forgets variables, which
-- keeps the environments agreeing (`Env`); `⊢sub-eff` is invisible up to bisimilarity
-- (`Erase.toT∞-sub`). Every other rule is fixed by the term's former, and a
-- term in its context has one type (`Uniqueness`), so the two derivations'
-- premises are at one type; their usages and grades may differ, and only
-- reach the meaning through `restrict` and `toT∞`. Each former's case is the
-- congruence of its semantic operation (`Layer`, `Conv`, `Sigop`). A
-- reference to the signature means one operation because Σ declares each
-- once (`OneName`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; call)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Signature using (OneName)

module Once.Metatheory.Coherence.Fundamental (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Grade
  using (fin; _·p_; positionGrade; Quantity; Zero; One; Many; Purity; pure; act; eff; mk-kind; _⊑π_;
         0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type
  using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; WFFun; respects-∘; ⟨⟩-∘; _⟨_⟩; _⟨_⟩F; Base; b-Unit; b-Int; b-Float; b-*; b-+;
         Unit; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F)
open import Once.Spec.Signature
  using (_∶_; constant; DeclType; ⌜_⌝; ⌜_⌝ᵈ; op)
open import Once.Spec.Context using (Ctx; _▸_; Usage; _∷_; _⊑ᵘ_; _+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; toT∞; fmap; bind; bindᵍ; sub; module νM)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toB; fromB; toL; fromL; foldM; conv)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv; Coherence)
import Once.Spec.Word as Word
open import Once.Metatheory.Types using (<:-unique; ⊑π-unique)
open import Once.Spec.Sub using (_<:_)
open import Once.Metatheory.Erase Σ using (toT∞-fmap)
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ
open import Once.Metatheory.Coherence.Loop Σ using (loopSame)
import Once.Metatheory.Coherence.Conversions Σ as Conversions
open import Once.Metatheory.Coherence.Conv Σ using (convSame)
open import Once.Metatheory.Coherence.Sigop Σ
open import Once.Metatheory.Coherence.Env Σ fmt S
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique; ⇒-inj; kind-inj)
open Names u
open import Once.Metatheory.Coherence.Leaves Σ fmt S

open DefSem

------------------------------------------------------------------------
-- The fundamental lemma
------------------------------------------------------------------------

module FL {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r r′ : Respects Δ ∅ₖ σ) where

  MM : Purity → Ty m → Set
  MM π A = M π ⟦ A ⟨ σ ⟩ ⟧ᵛ

  -- The second meaning, read at the first derivation's type.
  substM : ∀ π {A A′ : Ty m} → A′ ≡ A → MM π A′ → MM π A
  substM π refl x = x

  FL : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ t A A′ π π′} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A′ ! π′)
       (eq : A′ ≡ A) {γ γ′} → Agree σ Γ Ψ Ψ′ γ γ′
     → Rel π π′ (A ⟨ σ ⟩) (⟦ d ⟧ δ σ r γ) (substM π′ eq (⟦ d′ ⟧ δ σ r′ γ′))

  private
    rr : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ Ψ₀′ Ψ′ : Usage n} (p : Ψ₀ ⊑ᵘ Ψ) (p′ : Ψ₀′ ⊑ᵘ Ψ′) {γ γ′}
       → Agree σ Γ Ψ Ψ′ γ γ′ → Agree σ Γ Ψ₀ Ψ₀′ (restrict σ p γ) (restrict σ p′ γ′)
    rr p p′ ag = restrictˡ σ p (restrictʳ σ p′ ag)

  -- application, at one arrow type
  appH : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ Ψ₁′ Ψ₂′ q q′ π π″ π₁ π₂ π₁′ π₂′ A₁ A₂ B f x}
       → (A₁ ⇒[ mk-kind q π ] B) ≡ (A₂ ⇒[ mk-kind q′ π″ ] B)
       → (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A₁ ⇒[ mk-kind q π ] B ! π₁) (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A₁ ! positionGrade q π₂)
       → (df′ : Δ ⊩ Γ ⊢[ Ψ₁′ ] f ∷ A₂ ⇒[ mk-kind q′ π″ ] B ! π₁′) (dx′ : Δ ⊩ Γ ⊢[ Ψ₂′ ] x ∷ A₂ ! positionGrade q′ π₂′)
       → ∀ {γ γ′} → Agree σ Γ (Ψ₁ +ᵘ q *ᵘ Ψ₂) (Ψ₁′ +ᵘ q′ *ᵘ Ψ₂′) γ γ′
       → Rel _ _ (B ⟨ σ ⟩) (⟦ ⊢app df dx ⟧ δ σ r γ) (⟦ ⊢app df′ dx′ ⟧ δ σ r′ γ′)
  appH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = Zero} {A₁ = A₁} refl df dx df′ dx′ ag =
    relBindᵍ (FL df df′ refl (rr (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) (⊑ᵘ-+ˡ Ψ₁′ (Zero *ᵘ Ψ₂′)) ag)) (appZero {A = A₁ ⟨ σ ⟩})
  appH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = One} refl df dx df′ dx′ ag =
    relBindᵍ (FL df df′ refl (rr (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) (⊑ᵘ-+ˡ Ψ₁′ (One *ᵘ Ψ₂′)) ag)) λ sf →
    relBindᵍ (FL dx dx′ refl (rr (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂)))
                                 (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂′) (⊑ᵘ-+ʳ Ψ₁′ (One *ᵘ Ψ₂′))) ag)) λ sx → appOne sf sx
  appH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = Many} refl df dx df′ dx′ ag =
    relBindᵍ (FL df df′ refl (rr (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) (⊑ᵘ-+ˡ Ψ₁′ (Many *ᵘ Ψ₂′)) ag)) λ sf →
    relBindᵍ (FL dx dx′ refl (rr (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂)))
                                 (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂′) (⊑ᵘ-+ʳ Ψ₁′ (Many *ᵘ Ψ₂′))) ag)) λ sx → appMany sf sx

  letH : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ Ψ₁′ Ψ₂′ q π₁ π₂ π₁′ π₂′ A A′ B e b}
       → A ≡ A′
       → (d₁ : Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁) (d₂ : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂)
       → (d₁′ : Δ ⊩ Γ ⊢[ Ψ₁′ ] e ∷ A′ ! positionGrade q π₁′) (d₂′ : Δ ⊩ (Γ ▸ A′) ⊢[ q ∷ Ψ₂′ ] b ∷ B ! π₂′)
       → ∀ {γ γ′} → Agree σ Γ (Ψ₂ +ᵘ q *ᵘ Ψ₁) (Ψ₂′ +ᵘ q *ᵘ Ψ₁′) γ γ′
       → Rel _ _ (B ⟨ σ ⟩) (⟦ ⊢let d₁ d₂ ⟧ δ σ r γ) (⟦ ⊢let d₁′ d₂′ ⟧ δ σ r′ γ′)
  letH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = Zero} refl d₁ d₂ d₁′ d₂′ ag =
    FL d₂ d₂′ refl (rr (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) (⊑ᵘ-+ˡ Ψ₂′ (Zero *ᵘ Ψ₁′)) ag , tt)
  letH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = One} refl d₁ d₂ d₁′ d₂′ ag =
    relBindᵍ (FL d₁ d₁′ refl (rr (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁)))
                                 (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁′) (⊑ᵘ-+ʳ Ψ₂′ (One *ᵘ Ψ₁′))) ag)) λ sv →
    FL d₂ d₂′ refl (rr (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) (⊑ᵘ-+ˡ Ψ₂′ (One *ᵘ Ψ₁′)) ag , sv)
  letH {Ψ₁ = Ψ₁} {Ψ₂} {Ψ₁′} {Ψ₂′} {q = Many} refl d₁ d₂ d₁′ d₂′ ag =
    relBindᵍ (FL d₁ d₁′ refl (rr (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁)))
                                 (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁′) (⊑ᵘ-+ʳ Ψ₂′ (Many *ᵘ Ψ₁′))) ag)) λ sv →
    FL d₂ d₂′ refl (rr (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) (⊑ᵘ-+ˡ Ψ₂′ (Many *ᵘ Ψ₁′)) ag , sv)

  fstH : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ π π′ A B B′ p}
       → (A * B) ≡ (A * B′) → (d : Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] p ∷ A * B′ ! π′)
       → ∀ {γ γ′} → Agree σ Γ Ψ Ψ′ γ γ′ → Rel π π′ (A ⟨ σ ⟩) (⟦ ⊢fst d ⟧ δ σ r γ) (⟦ ⊢fst d′ ⟧ δ σ r′ γ′)
  fstH {A = A} {B} refl d d′ ag = relFmap (FL d d′ refl ag) (sameFst {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩})

  sndH : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ π π′ A A′ B p}
       → (A * B) ≡ (A′ * B) → (d : Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] p ∷ A′ * B ! π′)
       → ∀ {γ γ′} → Agree σ Γ Ψ Ψ′ γ γ′ → Rel π π′ (B ⟨ σ ⟩) (⟦ ⊢snd d ⟧ δ σ r γ) (⟦ ⊢snd d′ ⟧ δ σ r′ γ′)
  sndH {A = A} {B = B} refl d d′ ag = relFmap (FL d d′ refl ag) (sameSnd {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩})

  caseH : ∀ {n} {Γ : Ctx m n} {Ψs Ψ Ψs′ Ψ′ qℓ qr π₁ π₂ π₁′ π₂′ A B A′ B′ C e l rt}
        → (A + B) ≡ (A′ + B′)
        → (ds : Δ ⊩ Γ ⊢[ Ψs ] e ∷ A + B ! π₁) (dl : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π₂) (dr : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψ ] rt ∷ C ! π₂)
        → (ds′ : Δ ⊩ Γ ⊢[ Ψs′ ] e ∷ A′ + B′ ! π₁′) (dl′ : Δ ⊩ (Γ ▸ A′) ⊢[ qℓ ∷ Ψ′ ] l ∷ C ! π₂′)
          (dr′ : Δ ⊩ (Γ ▸ B′) ⊢[ qr ∷ Ψ′ ] rt ∷ C ! π₂′)
        → ∀ {γ γ′} → Agree σ Γ (Ψs +ᵘ Ψ) (Ψs′ +ᵘ Ψ′) γ γ′
        → Rel _ _ (C ⟨ σ ⟩) (⟦ ⊢case ds dl dr ⟧ δ σ r γ) (⟦ ⊢case ds′ dl′ dr′ ⟧ δ σ r′ γ′)
  caseH {Ψs = Ψs} {Ψ} {Ψs′} {Ψ′} {qℓ} {qr} {π₁} {π₂} {π₁′} {π₂′} {A = A} {B} {C = C} refl ds dl dr ds′ dl′ dr′ ag =
    relBindᵍ (FL ds ds′ refl (rr (⊑ᵘ-+ˡ Ψs Ψ) (⊑ᵘ-+ˡ Ψs′ Ψ′) ag))
      (λ {w} {w′} sw → caseRel {A ⟨ σ ⟩} {B ⟨ σ ⟩} {C ⟨ σ ⟩} {π₂} {π₂′}
               (λ {a} {a′} sa → FL dl dl′ refl (rr (⊑ᵘ-+ʳ Ψs Ψ) (⊑ᵘ-+ʳ Ψs′ Ψ′) ag , slotSame σ A qℓ {a} {a′} sa))
               (λ {b} {b′} sb → FL dr dr′ refl (rr (⊑ᵘ-+ʳ Ψs Ψ) (⊑ᵘ-+ʳ Ψs′ Ψ′) ag , slotSame σ B qr {b} {b′} sb))
               {w} {w′} sw)

  foldH : ∀ {n} {Γ : Ctx m n} {Ψa Ψt Ψa′ Ψt′ π π′ π₁ π₂ π₁′ π₂′ F A alg t}
        → (⟦ F ⟧F A ⇒[ mk-kind Many π ] A) ≡ (⟦ F ⟧F A ⇒[ mk-kind Many π′ ] A)
        → (wf : WFFun Δ F) (da : Δ ⊩ Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! π₁)
          (dt : Δ ⊩ Γ ⊢[ Ψt ] t ∷ μ F ! π₂)
        → (wf′ : WFFun Δ F) (da′ : Δ ⊩ Γ ⊢[ Ψa′ ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π′ ] A ! π₁′)
          (dt′ : Δ ⊩ Γ ⊢[ Ψt′ ] t ∷ μ F ! π₂′)
        → ∀ {γ γ′} → Agree σ Γ (Many *ᵘ Ψa +ᵘ Ψt) (Many *ᵘ Ψa′ +ᵘ Ψt′) γ γ′
        → Rel _ _ (A ⟨ σ ⟩) (⟦ ⊢fold wf da dt ⟧ δ σ r γ) (⟦ ⊢fold wf′ da′ dt′ ⟧ δ σ r′ γ′)
  foldH {Ψa = Ψa} {Ψt} {Ψa′} {Ψt′} {π} {F = F} {A} refl wf da dt wf′ da′ dt′ ag =
    relBindᵍ (FL da da′ refl (rr (⊑ᵘ-trans (⊑ᵘ-*Many Ψa) (⊑ᵘ-+ˡ (Many *ᵘ Ψa) Ψt))
                                 (⊑ᵘ-trans (⊑ᵘ-*Many Ψa′) (⊑ᵘ-+ˡ (Many *ᵘ Ψa′) Ψt′)) ag)) λ {alg} {alg′} salg →
    relBindᵍ (FL dt dt′ refl (rr (⊑ᵘ-+ʳ (Many *ᵘ Ψa) Ψt) (⊑ᵘ-+ʳ (Many *ᵘ Ψa′) Ψt′) ag)) λ {v} {v′} sv →
    subst (λ w → Rel π π (A ⟨ σ ⟩) (foldM π (code (F ⟨ σ ⟩F)) (λ l → alg (fromL σ F A l)) v)
                                     (foldM π (code (F ⟨ σ ⟩F)) (λ l → alg′ (fromL σ F A l)) w))
          (sameμ sv)
          (Fold.foldRel π (code (F ⟨ σ ⟩F)) (A ⟨ σ ⟩) _ _
             (λ le → appMany salg (Functor.fromL-same σ r wf A le)) v)

  unfoldH : ∀ {n} {Γ : Ctx m n} {Ψc Ψs Ψc′ Ψs′ f π₁ π₂ π₁′ π₂′ F A A′ c a}
          → (A ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A) ≡ (A′ ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A′)
          → (wf : WFFun Δ F) (dc : Δ ⊩ Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A ! π₁) (da : Δ ⊩ Γ ⊢[ Ψs ] a ∷ A ! π₂)
          → (wf′ : WFFun Δ F) (dc′ : Δ ⊩ Γ ⊢[ Ψc′ ] c ∷ A′ ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A′ ! π₁′)
            (da′ : Δ ⊩ Γ ⊢[ Ψs′ ] a ∷ A′ ! π₂′)
          → ∀ {γ γ′} → Agree σ Γ (Many *ᵘ Ψc +ᵘ Ψs) (Many *ᵘ Ψc′ +ᵘ Ψs′) γ γ′
          → Rel _ _ (ν F f ⟨ σ ⟩) (⟦ ⊢unfold wf dc da ⟧ δ σ r γ) (⟦ ⊢unfold wf′ dc′ da′ ⟧ δ σ r′ γ′)
  unfoldH {Ψc = Ψc} {Ψs} {Ψc′} {Ψs′} {f} {F = F} {A} refl wf dc da wf′ dc′ da′ ag =
    relBindᵍ (FL dc dc′ refl (rr (⊑ᵘ-trans (⊑ᵘ-*Many Ψc) (⊑ᵘ-+ˡ (Many *ᵘ Ψc) Ψs))
                                 (⊑ᵘ-trans (⊑ᵘ-*Many Ψc′) (⊑ᵘ-+ˡ (Many *ᵘ Ψc′) Ψs′)) ag)) λ {c} {c′} sc →
    relFmap (FL da da′ refl (rr (⊑ᵘ-+ʳ (Many *ᵘ Ψc) Ψs) (⊑ᵘ-+ʳ (Many *ᵘ Ψc′) Ψs′) ag)) λ sa n →
      Ana.anaRel f (code (F ⟨ σ ⟩F)) (A ⟨ σ ⟩) (λ x → fmap (fin f) (toL σ F A) (c x)) (λ x → fmap (fin f) (toL σ F A) (c′ x))
        (λ {a} {a′} s → ≈-Relatedˡ (toT∞-fmap (fin f) (toL σ F A) (c a)) (≈-Relatedʳ (toT∞-fmap (fin f) (toL σ F A) (c′ a′))
                          (relatedFmap (runs (appMany {π = fin f} sc s)) (Functor.toL-same σ r wf A))))
        n sa

  outH : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ f f′ π₁ π₁′ F F′ t}
       → ν F f ≡ ν F′ f′ → (eq : ⟦ F′ ⟧F (ν F′ f′) ≡ ⟦ F ⟧F (ν F f))
       → (wf : WFFun Δ F) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ ν F f ! π₁) (wf′ : WFFun Δ F′) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ ν F′ f′ ! π₁′)
       → ∀ {γ γ′} → Agree σ Γ Ψ Ψ′ γ γ′
       → Rel _ _ ((⟦ F ⟧F (ν F f)) ⟨ σ ⟩) (⟦ ⊢out wf d ⟧ δ σ r γ) (substM (π₁′ ·p fin f′) eq (⟦ ⊢out wf′ d′ ⟧ δ σ r′ γ′))
  outH {f = f} {F = F} refl refl wf d wf′ d′ ag =
    relBindᵍ (FL d d′ refl ag) λ {v} {v′} sv → rel (
      ≈-Relatedˡ (toT∞-fmap (fin f) (fromL σ F (ν F f)) (outν v))
        (≈-Relatedʳ (toT∞-fmap (fin f) (fromL σ F (ν F f)) (outν v′))
          (relatedFmap (outRel f (code (F ⟨ σ ⟩F)) sv)
                    (λ h → Functor.fromL-same σ r wf (ν F f) (LayerEq-∀ (code (F ⟨ σ ⟩F)) h)))))

  iterH : ∀ {n} {Γ : Ctx m n} {Ψf Ψs Ψf′ Ψs′ π₁ π₂ π₁′ π₂′ A A′ B f a}
        → (A ⇒[ mk-kind Many act ] (B + A)) ≡ (A′ ⇒[ mk-kind Many act ] (B + A′))
        → (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind Many act ] (B + A) ! π₁) (ds : Δ ⊩ Γ ⊢[ Ψs ] a ∷ A ! π₂)
        → (df′ : Δ ⊩ Γ ⊢[ Ψf′ ] f ∷ A′ ⇒[ mk-kind Many act ] (B + A′) ! π₁′) (ds′ : Δ ⊩ Γ ⊢[ Ψs′ ] a ∷ A′ ! π₂′)
        → ∀ {γ γ′} → Agree σ Γ (Many *ᵘ Ψf +ᵘ Ψs) (Many *ᵘ Ψf′ +ᵘ Ψs′) γ γ′
        → Rel _ _ (B ⟨ σ ⟩) (⟦ ⊢iter df ds ⟧ δ σ r γ) (⟦ ⊢iter df′ ds′ ⟧ δ σ r′ γ′)
  iterH {Ψf = Ψf} {Ψs} {Ψf′} {Ψs′} {A = A} {B = B} refl df ds df′ ds′ ag =
    relBindᵍ (FL df df′ refl (rr (⊑ᵘ-trans (⊑ᵘ-*Many Ψf) (⊑ᵘ-+ˡ (Many *ᵘ Ψf) Ψs))
                                 (⊑ᵘ-trans (⊑ᵘ-*Many Ψf′) (⊑ᵘ-+ˡ (Many *ᵘ Ψf′) Ψs′)) ag)) λ {f} {f′} sf →
    relBindᵍ (FL ds ds′ refl (rr (⊑ᵘ-+ʳ (Many *ᵘ Ψf) Ψs) (⊑ᵘ-+ʳ (Many *ᵘ Ψf′) Ψs′) ag)) λ sa →
    rel (loopSame (A ⟨ σ ⟩) (B ⟨ σ ⟩) f f′ (λ s → runs (appMany {π = act} sf s)) sa)

  coerceH : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ π π′ A B t} (p p′ : A <: B)
          → (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (d′ : Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A ! π′)
          → ∀ {γ γ′} → Agree σ Γ Ψ Ψ′ γ γ′
          → Rel π π′ (B ⟨ σ ⟩) (⟦ ⊢coerce p d ⟧ δ σ r γ) (⟦ ⊢coerce p′ d′ ⟧ δ σ r′ γ′)
  coerceH p p′ d d′ ag rewrite <:-unique p′ p = relFmap (FL d d′ refl ag) (convSame σ p)

  sigopH : ∀ {c t} (mem mem′ : (c ∶ t) ∈ Σ)
         → Rel pure pure (⌜ t ⌝ᵈ ⟨ σ ⟩) (sigopᵛ σ c t mem (model δ)) (sigopᵛ σ c t mem′ (model δ))
  sigopH {c} {t} mem mem′ rewrite mem-unique mem′ mem = relPure (sigopRefl σ c t mem (model δ))

  -- Peeling the structural rules.
  FL (⊢sub-use p d) d′ eq ag = FL d d′ eq (restrictˡ σ p ag)
  FL (⊢sub-eff g d) d′ eq ag = relSubˡ g (FL d d′ eq ag)
  {-# CATCHALL #-}
  FL d (⊢sub-use p d′) refl ag = FL d d′ refl (restrictʳ σ p ag)
  {-# CATCHALL #-}
  FL d (⊢sub-eff g d′) refl ag = relSubʳ g (FL d d′ refl ag)
  -- One former, on both sides.
  FL (⊢var i) (⊢var .i) refl ag = relPure (lookupAgree σ _ i ag)
  FL (⊢lam {q = Zero} {π = π} {A} {B} 0≤q d) (⊢lam 0≤q d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Zero π ] B) ⟨ σ ⟩} (lamZero {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} (FL d d′ refl (ag , tt)))
  FL (⊢lam {q = One} {π = π} {A} {B} 0≤q d) (⊢lam 0≤q d′) refl ag =
    relPure {A = (A ⇒[ mk-kind One π ] B) ⟨ σ ⟩} (lamOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , tt))
  FL (⊢lam {q = One} {π = π} {A} {B} 0≤q d) (⊢lam 1≤1 d′) refl ag =
    relPure {A = (A ⇒[ mk-kind One π ] B) ⟨ σ ⟩} (lamOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , tt))
  FL (⊢lam {q = One} {π = π} {A} {B} 1≤1 d) (⊢lam 0≤q d′) refl ag =
    relPure {A = (A ⇒[ mk-kind One π ] B) ⟨ σ ⟩} (lamOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , tt))
  FL (⊢lam {q = One} {π = π} {A} {B} 1≤1 d) (⊢lam 1≤1 d′) refl ag =
    relPure {A = (A ⇒[ mk-kind One π ] B) ⟨ σ ⟩} (lamOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , sa))
  FL (⊢lam {q = Many} {π = π} {A} {B} 0≤q d) (⊢lam 0≤q d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , tt))
  FL (⊢lam {q = Many} {π = π} {A} {B} 0≤q d) (⊢lam 1≤ω d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , tt))
  FL (⊢lam {q = Many} {π = π} {A} {B} 0≤q d) (⊢lam ω≤ω d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , tt))
  FL (⊢lam {q = Many} {π = π} {A} {B} 1≤ω d) (⊢lam 0≤q d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , tt))
  FL (⊢lam {q = Many} {π = π} {A} {B} 1≤ω d) (⊢lam 1≤ω d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , sa))
  FL (⊢lam {q = Many} {π = π} {A} {B} 1≤ω d) (⊢lam ω≤ω d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , sa))
  FL (⊢lam {q = Many} {π = π} {A} {B} ω≤ω d) (⊢lam 0≤q d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , tt))
  FL (⊢lam {q = Many} {π = π} {A} {B} ω≤ω d) (⊢lam 1≤ω d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , sa))
  FL (⊢lam {q = Many} {π = π} {A} {B} ω≤ω d) (⊢lam ω≤ω d′) refl ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → FL d d′ refl (ag , sa))
  FL (⊢app df dx) (⊢app df′ dx′) refl ag = appH (ty-unique df df′) df dx df′ dx′ ag
  FL (⊢let d₁ d₂) (⊢let d₁′ d₂′) refl ag = letH (ty-unique d₁ d₁′) d₁ d₂ d₁′ d₂′ ag
  FL ⊢unit ⊢unit refl ag = relPure tt
  FL (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} {π₁} {π₂} {A} {B} da db) (⊢pair {Ψ₁ = Ψ₁′} {Ψ₂′} {π₁′} {π₂′} da′ db′) refl ag =
    relBindᵍ {π₁} {π₂} {π₁′} {π₂′} {A ⟨ σ ⟩} {(A * B) ⟨ σ ⟩} (FL da da′ refl (rr (⊑ᵘ-+ˡ Ψ₁ Ψ₂) (⊑ᵘ-+ˡ Ψ₁′ Ψ₂′) ag)) λ sa →
    relFmap {π₂} {π₂′} {B ⟨ σ ⟩} {(A * B) ⟨ σ ⟩} (FL db db′ refl (rr (⊑ᵘ-+ʳ Ψ₁ Ψ₂) (⊑ᵘ-+ʳ Ψ₁′ Ψ₂′) ag)) λ sb →
      samePair {A ⟨ σ ⟩} {B ⟨ σ ⟩} sa sb
  FL (⊢fst d) (⊢fst d′) refl ag = fstH (ty-unique d d′) d d′ ag
  FL (⊢snd d) (⊢snd d′) refl ag = sndH (ty-unique d d′) d d′ ag
  FL (⊢inl {π = π} {A} {B} d) (⊢inl {π = π′} d′) refl ag = relFmap {π} {π′} (FL d d′ refl ag) (sameInl {A ⟨ σ ⟩} {B ⟨ σ ⟩})
  FL (⊢inr {π = π} {A} {B} d) (⊢inr {π = π′} d′) refl ag = relFmap {π} {π′} (FL d d′ refl ag) (sameInr {A ⟨ σ ⟩} {B ⟨ σ ⟩})
  FL (⊢case ds dl dr) (⊢case ds′ dl′ dr′) refl ag = caseH (ty-unique ds ds′) ds dl dr ds′ dl′ dr′ ag
  FL (⊢absurd {π = π} d) (⊢absurd {π = π′} d′) refl ag = relBind {π} {π′} (FL d d′ refl ag) λ {x} _ → ⊥-elim x
  FL (⊢roll {π = π} wf d) (⊢roll {π = π′} wf′ d′) refl ag = relFmap {π} {π′} (FL d d′ refl ag) λ s → Functor.roll-same σ r wf s
  FL (⊢fold wf da dt) (⊢fold wf′ da′ dt′) refl ag = foldH (ty-unique da da′) wf da dt wf′ da′ dt′ ag
  FL (⊢unfold wf dc da) (⊢unfold wf′ dc′ da′) refl ag = unfoldH (ty-unique dc dc′) wf dc da wf′ dc′ da′ ag
  FL (⊢out wf d) (⊢out wf′ d′) eq ag = outH (ty-unique d d′) eq wf d wf′ d′ ag
  FL (⊢iter df ds) (⊢iter df′ ds′) refl ag = iterH (ty-unique df df′) df ds df′ ds′ ag
  FL (⊢coerce p d) (⊢coerce p′ d′) refl ag = coerceH p p′ d d′ ag
  FL ⊢lit-int ⊢lit-int refl ag = relPure {A = Int} refl
  FL ⊢lit-float ⊢lit-float refl ag = relPure {A = Float} refl
  FL (⊢prim {π = π} p d) (⊢prim {π = π′} .p d′) refl ag = relFmap {π} {π′} (FL d d′ refl ag) (primSame σ p)
  FL (⊢sigop mem) (⊢sigop mem′) refl ag = sigopH mem mem′
  FL (⊢ref d τ rd) (⊢ref .d .τ rd′) refl ag =
    relPure (substSame (sym (⟨⟩-∘ (type (S !! d)) τ σ))
                       (sd d (λ i → τ i ⟨ σ ⟩) (respects-∘ rd r) (respects-∘ rd′ r′)))

------------------------------------------------------------------------
-- Coherence
------------------------------------------------------------------------

coherence : Coherence Σ fmt S
coherence = record
  { coherent = λ {m} {n} {Δ} {Γ} {Ψ} {t} {A} {π} d d′ δ sd σ r r′ γ sγ →
      toObserved (runs (FL.FL δ sd σ r r′ d d′ refl (selfAgree σ Γ Ψ γ sγ)))
  ; conv-id = λ σ p s → Conversions.conv-id σ p s
  ; conv-∘  = λ σ p q r s → Conversions.conv-∘ σ p q r s }
