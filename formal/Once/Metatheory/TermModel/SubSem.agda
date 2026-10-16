{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TermModel.SubSem — substitution, in the meaning: a term
-- with its variables replaced by pure terms means, in an environment, what
-- the original means in the environment of the replacements' values
-- (`subSem`). With the fundamental lemma this gives `let-β`: a pure `let`
-- means its substitution.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Metatheory using (OneName)

module Once.Metatheory.TermModel.SubSem (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Once.Spec.Grade
  using (Quantity; Zero; One; Many; Purity; pure; eff⁺; mk-kind; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type
  using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; respects-∘; ⟨⟩-∘; _⟨_⟩; _⟨_⟩F; Int; Float; _⇒[_]_; _*_; _+_; μ; ν; ⟦_⟧F; Unit)
open import Once.Spec.Context using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_; ⊑ᵘ-trans)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; fmap; module νM)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM; anaM)
open import Once.Spec.Equivalence Σ using (Same; SameM)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Erase Σ using (toT∞-fmap)
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Coherence.Conv Σ using (convSame)
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree; selfAgree; restrictˡ; restrictʳ)
open import Once.Metatheory.Coherence.Leaves Σ fmt S using (sigopRefl; sigop⁺Refl; primSame; substSame; slotSame; caseRel)
open import Once.Metatheory.Coherence.Fundamental Σ u fmt S using (module FL)
open import Once.Metatheory.TermModel.Usage
open import Once.Metatheory.TermModel.Subst Σ S
open import Once.Metatheory.TermModel.Ren Σ fmt S using (module RenSem)
open import Once.Metatheory.TermModel.Val Σ fmt S

open DefSem

module SubSem {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where
  open TSub

  -- At each variable the original holds, the replacement's value (in any
  -- environment forgetting down to its usage) is the same as the original's.
  SubAgree : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σS : TSub {Δ = Δ} Γ Γ′) (Ψ : Usage n′)
           → Env σ Γ (Ψ ·ᵐ usage σS) → Env σ Γ′ Ψ → Set
  SubAgree {Γ′ = Γ′} σS Ψ γ γ′ =
    ∀ i (nz : NZ (At Ψ i)) (p : usage σS i ⊑ᵘ Ψ ·ᵐ usage σS)
    → Same (lookup Γ′ i ⟨ σ ⟩) (⟦ typed σS i ⟧ δ σ r (restrict σ p γ)) (val σ γ′ i nz)

  subRestrict : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σS : TSub Γ Γ′) {Ψ₀ Ψ : Usage n′} {X}
                (P : Ψ₀ ·ᵐ usage σS ⊑ᵘ X) (Q : X ⊑ᵘ Ψ ·ᵐ usage σS) (p′ : Ψ₀ ⊑ᵘ Ψ) {γ γ′}
              → SubAgree σS Ψ γ γ′ → SubAgree σS Ψ₀ (restrict σ P (restrict σ Q γ)) (restrict σ p′ γ′)
  subRestrict σS P Q p′ {γ} {γ′} ag i nz p =
    subst₂ (λ x y → Same _ (⟦ typed σS i ⟧ δ σ r x) y)
           (sym (trans (cong (restrict σ p) (restrict-∘ σ P Q γ)) (restrict-∘ σ p (⊑ᵘ-trans P Q) γ)))
           (sym (restrict-val σ p′ γ′ i nz))
           (ag i (nz-mono p′ i nz) (⊑ᵘ-trans p (⊑ᵘ-trans P Q)))

  subRestrict₁ : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σS : TSub Γ Γ′) {Ψ₀ Ψ : Usage n′}
                 (P : Ψ₀ ·ᵐ usage σS ⊑ᵘ Ψ ·ᵐ usage σS) (p′ : Ψ₀ ⊑ᵘ Ψ) {γ γ′}
               → SubAgree σS Ψ γ γ′ → SubAgree σS Ψ₀ (restrict σ P γ) (restrict σ p′ γ′)
  subRestrict₁ σS P p′ {γ} {γ′} ag i nz p =
    subst₂ (λ x y → Same _ (⟦ typed σS i ⟧ δ σ r x) y)
           (sym (restrict-∘ σ p P γ)) (sym (restrict-val σ p′ γ′ i nz))
           (ag i (nz-mono p′ i nz) (⊑ᵘ-trans p P))

  private
    slotSameNZ : ∀ {A : Ty m} q {x x′} → SlotAgree σ A q q x x′ → (nz : NZ q) → Same (A ⟨ σ ⟩) (slotVal σ q x nz) (slotVal σ q x′ nz)
    slotSameNZ One  s nz = s
    slotSameNZ Many s nz = s

    -- The Γ side of a slot is the same as itself.
    slotSelf : ∀ {A : Ty m} q {x x′} → SlotAgree σ A q q x x′ → (nz : NZ q) → Same (A ⟨ σ ⟩) (slotVal σ q x nz) (slotVal σ q x nz)
    slotSelf {A} q s nz = Same-trans (A ⟨ σ ⟩) (slotSameNZ q s nz) (Same-sym (A ⟨ σ ⟩) (slotSameNZ q s nz))

  selfExt : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {q} {γ : Env σ Γ Ψ} {x x′}
          → SelfSame σ γ → SlotAgree σ A q q x x′ → SelfSame σ {Γ = Γ ▸ A} {Ψ = q ∷ Ψ} (γ , x)
  selfExt {q = q} ss s zero    nz = slotSelf q s nz
  selfExt         ss s (suc i) nz = ss i nz

  -- Under a binder: the new variable is itself, the others are weakened.
  subExts : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σS : TSub Γ Γ′) {A : Ty m} (q : Quantity) (Ψ : Usage n′) {γ γ′ x x′}
          → SelfSame σ γ → SubAgree σS Ψ γ γ′ → SlotAgree σ A q q x x′
          → SubAgree (extsT {A = A} σS) (q ∷ Ψ) (restrict σ (⊑ᵘ-≡ (·ᵐ-exts {A = A} σS q Ψ)) (γ , x)) (γ′ , x′)
  subExts {n} {Γ = Γ} σS {A} q Ψ {γ} {γ′} {x} {x′} ss ag sx zero nz p =
    subst (λ w → Same (A ⟨ σ ⟩) w (slotVal σ q x′ nz))
          (sym (trans (lookup-val σ (Γ ▸ A) zero (restrict σ p e₂))
               (trans (restrict-val σ p e₂ zero tt) (restrict-val σ E γx zero _))))
          (subst (λ w → Same (A ⟨ σ ⟩) (slotVal σ q x w) (slotVal σ q x′ nz)) (nz-irr nz _) (slotSameNZ q sx nz))
    where
      E = ⊑ᵘ-≡ (·ᵐ-exts {A = A} σS q Ψ)
      γx : Env σ (Γ ▸ A) (q ∷ (Ψ ·ᵐ usage σS))
      γx = γ , x
      e₂ : Env σ (Γ ▸ A) ((q ∷ Ψ) ·ᵐ usage (extsT {A = A} σS))
      e₂ = restrict σ E γx
  subExts {n} {Γ = Γ} {Γ′ = Γ′} σS {A} q Ψ {γ} {γ′} {x} {x′} ss ag sx (suc j) nz p =
    Same-trans (lookup Γ′ j ⟨ σ ⟩)
      (relPure⁻ (RenSem.renSem δ sd σ r (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip (cid Γ)) (typed σS j)
                   {γ′ = restrict σ W (restrict σ p (restrict σ E γx))} {γ = restrict σ p₀ γ}
                   (thin-cid σ Γ (λ k nz′ nz″ →
                      subst₂ (Same _)
                        (sym (trans (restrict-val σ W (restrict σ p (restrict σ E γx)) (suc k) nz′)
                             (trans (restrict-val σ p (restrict σ E γx) (suc k) _) (restrict-val σ E γx (suc k) _))))
                        (sym (restrict-val σ p₀ γ k nz″))
                        (subst (λ w → Same _ (val σ γ k w) (val σ γ k _)) (nz-irr _ _) (ss k _))))))
      (ag j nz p₀)
    where
      E  = ⊑ᵘ-≡ (·ᵐ-exts {A = A} σS q Ψ)
      W  = ⊑ᵘ-≡ (cong (Zero ∷_) (θ*-id (usage σS j)))
      p₀ = ·ᵐ-sup Ψ (usage σS) j nz
      γx : Env σ (Γ ▸ A) (q ∷ (Ψ ·ᵐ usage σS))
      γx = γ , x

  subSem : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σS : TSub Γ Γ′) {Ψ t A π} (d : Δ ⊩ Γ′ ⊢[ Ψ ] t ∷ A ! π) {γ γ′}
         → SelfSame σ γ → SubAgree σS Ψ γ γ′
         → Rel π π (A ⟨ σ ⟩) (⟦ sub-⊢ σS d ⟧ δ σ r γ) (⟦ d ⟧ δ σ r γ′)

  private
    sr : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σS : TSub Γ Γ′) {Ψ₀ Ψ : Usage n′} {X}
         (P : Ψ₀ ·ᵐ usage σS ⊑ᵘ X) (Q : X ⊑ᵘ Ψ ·ᵐ usage σS) (p′ : Ψ₀ ⊑ᵘ Ψ) {γ γ′}
       → SelfSame σ γ → SubAgree σS Ψ γ γ′
       → SelfSame σ (restrict σ P (restrict σ Q γ)) × SubAgree σS Ψ₀ (restrict σ P (restrict σ Q γ)) (restrict σ p′ γ′)
    sr σS P Q p′ {γ} ss ag = selfSame-restrict σ P {γ = restrict σ Q γ} (selfSame-restrict σ Q {γ = γ} ss) , subRestrict σS P Q p′ ag

    extᵃ : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σS : TSub Γ Γ′) {A : Ty m} (q : Quantity) (Ψ : Usage n′) {γ γ′ x x′}
        → SelfSame σ γ → SubAgree σS Ψ γ γ′ → SlotAgree σ A q q x x′
        → SelfSame σ (restrict σ (⊑ᵘ-≡ (·ᵐ-exts {A = A} σS q Ψ)) (γ , x))
          × SubAgree (extsT {A = A} σS) (q ∷ Ψ) (restrict σ (⊑ᵘ-≡ (·ᵐ-exts {A = A} σS q Ψ)) (γ , x)) (γ′ , x′)
    extᵃ σS {A} q Ψ {γ} {γ′} {x} ss ag sx = selfSame-restrict σ (⊑ᵘ-≡ (·ᵐ-exts {A = A} σS q Ψ)) {γ = (γ , x)} (selfExt {A = A} {q = q} ss sx) , subExts σS q Ψ ss ag sx

    under : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σS : TSub Γ Γ′) {A : Ty m} (q : Quantity) (Ψ : Usage n′)
            {B π t} (d : Δ ⊩ (Γ′ ▸ A) ⊢[ q ∷ Ψ ] t ∷ B ! π) {γ γ′ x x′}
          → SelfSame σ γ → SubAgree σS Ψ γ γ′ → SlotAgree σ A q q x x′
          → Rel π π (B ⟨ σ ⟩) (⟦ cast (·ᵐ-exts {A = A} σS q Ψ) (sub-⊢ (extsT σS) d) ⟧ δ σ r (γ , x)) (⟦ d ⟧ δ σ r (γ′ , x′))
    under σS q Ψ d ss ag sx = let (ss′ , ag′) = extᵃ σS q Ψ ss ag sx in subSem (extsT σS) d ss′ ag′

  subSem σS (⊢var {Γ = Γ′} i) {γ′ = γ′} ss ag =
    relPure (subst (λ w → Same _ _ w) (sym (lookup-val σ Γ′ i γ′))
                   (ag i (nz-single i) (⊑ᵘ-≡ (sym (·ᵐ-single i (usage σS))))))
  subSem σS (⊢lam {Ψ = Ψ} {q = Zero} {π = π} {A} {B} 0≤q d) ss ag =
    relPure {A = (A ⇒[ mk-kind Zero π ] B) ⟨ σ ⟩} (lamZero {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} (under σS Zero Ψ d ss ag tt))
  subSem σS (⊢lam {Ψ = Ψ} {q = One} {π = π} {A} {B} 0≤q d) ss ag =
    relPure {A = (A ⇒[ mk-kind One π ] B) ⟨ σ ⟩} (lamOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → under σS Zero Ψ d ss ag tt)
  subSem σS (⊢lam {Ψ = Ψ} {q = Many} {π = π} {A} {B} 0≤q d) ss ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → under σS Zero Ψ d ss ag tt)
  subSem σS (⊢lam {Ψ = Ψ} {π = π} {A} {B} 1≤1 d) ss ag =
    relPure {A = (A ⇒[ mk-kind One π ] B) ⟨ σ ⟩} (lamOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → under σS One Ψ d ss ag sa)
  subSem σS (⊢lam {Ψ = Ψ} {π = π} {A} {B} 1≤ω d) ss ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → under σS One Ψ d ss ag sa)
  subSem σS (⊢lam {Ψ = Ψ} {π = π} {A} {B} ω≤ω d) ss ag =
    relPure {A = (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩} (lamMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} λ sa → under σS Many Ψ d ss ag sa)
  subSem σS (⊢app {q = Zero} {A = A} df dx) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS df ss₁ ag₁) (appZero {A = A ⟨ σ ⟩})
  subSem σS (⊢app {q = One} df dx) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS df ss₁ ag₁) λ sf → relBindᵍ (subSem σS dx ss₂ ag₂) λ sx → appOne sf sx
  subSem σS (⊢app {q = Many} df dx) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS df ss₁ ag₁) λ sf → relBindᵍ (subSem σS dx ss₂ ag₂) λ sx → appMany sf sx
  subSem σS (⊢let {Ψ₂ = Ψ₂} {q = Zero} d₁ d₂) ss ag =
    let (ss₂ , ag₂) = sr σS _ _ _ ss ag in under σS Zero Ψ₂ d₂ ss₂ ag₂ tt
  subSem σS (⊢let {Ψ₂ = Ψ₂} {q = One} d₁ d₂) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS d₁ ss₁ ag₁) λ sv → under σS One Ψ₂ d₂ ss₂ ag₂ sv
  subSem σS (⊢let {Ψ₂ = Ψ₂} {q = Many} d₁ d₂) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS d₁ ss₁ ag₁) λ sv → under σS Many Ψ₂ d₂ ss₂ ag₂ sv
  subSem σS ⊢unit ss ag = relPure (λ n → tt)
  subSem σS (⊢pair {π₁ = π₁} {π₂} {A} {B} da db) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ {π₁} {π₂} {π₁} {π₂} {A ⟨ σ ⟩} {(A * B) ⟨ σ ⟩} (subSem σS da ss₁ ag₁) λ sa →
    relFmap {π₂} {π₂} {B ⟨ σ ⟩} {(A * B) ⟨ σ ⟩} (subSem σS db ss₂ ag₂) λ sb → samePair {A ⟨ σ ⟩} {B ⟨ σ ⟩} sa sb
  subSem σS (⊢fst {A = A} {B} d) ss ag = relFmap (subSem σS d ss ag) (sameFst {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩})
  subSem σS (⊢snd {A = A} {B} d) ss ag = relFmap (subSem σS d ss ag) (sameSnd {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩})
  subSem σS (⊢inl {π = π} {A} {B} d) ss ag = relFmap {π} {π} (subSem σS d ss ag) (sameInl {A ⟨ σ ⟩} {B ⟨ σ ⟩})
  subSem σS (⊢inr {π = π} {A} {B} d) ss ag = relFmap {π} {π} (subSem σS d ss ag) (sameInr {A ⟨ σ ⟩} {B ⟨ σ ⟩})
  subSem σS (⊢case {Ψ = Ψ} {qℓ} {qr} {π₁} {π₂} {A} {B} {C} ds dl dr) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS ds ss₁ ag₁) λ {w} {w′} sw →
      caseRel {A ⟨ σ ⟩} {B ⟨ σ ⟩} {C ⟨ σ ⟩} {π₂} {π₂}
        (λ {a} {a′} sa → under σS qℓ Ψ dl ss₂ ag₂ (slotSame σ A qℓ {a} {a′} sa))
        (λ {b} {b′} sb → under σS qr Ψ dr ss₂ ag₂ (slotSame σ B qr {b} {b′} sb))
        {w} {w′} sw
  subSem σS (⊢absurd {π = π} d) ss ag = relBind {π} {π} (subSem σS d ss ag) λ {x} _ → ⊥-elim x
  subSem σS (⊢roll {π = π} wf d) ss ag = relFmap {π} {π} (subSem σS d ss ag) λ s n → Functor.roll-same σ r wf s
  subSem σS (⊢fold {π = π} {F = F} {A} e wf da dt) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS da ss₁ ag₁) λ {alg} {alg′} salg →
    relBindᵍ (subSem σS dt ss₂ ag₂) λ {v} {v′} sv →
    subst (λ w → Rel π π (A ⟨ σ ⟩) (foldM π e (code (F ⟨ σ ⟩F)) (λ l → alg (fromL σ F A l)) v)
                                     (foldM π e (code (F ⟨ σ ⟩F)) (λ l → alg′ (fromL σ F A l)) w))
          (sameμ sv)
          (Fold.foldRel π e (code (F ⟨ σ ⟩F)) (A ⟨ σ ⟩) _ _ (λ le → appMany salg (Functor.fromL-same σ r wf A le)) v)
  subSem σS (⊢unfold {π = π} {F = F} {A} wf dc da) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS dc ss₁ ag₁) λ {c₁} {c₂} sc →
    relFmap (subSem σS da ss₂ ag₂) λ sa n →
      Ana.anaRel π (code (F ⟨ σ ⟩F)) (A ⟨ σ ⟩) (λ x → fmap π (toL σ F A) (c₁ x)) (λ x → fmap π (toL σ F A) (c₂ x))
        (λ {a} {a′} s → ≈-TreeRelˡ (toT∞-fmap π (toL σ F A) (c₁ a)) (≈-TreeRelʳ (toT∞-fmap π (toL σ F A) (c₂ a′))
                          (treeFmap (tree (appMany {π = π} sc s)) (Functor.toL-same σ r wf A))))
        n sa
  subSem σS (⊢out {π = π} {F = F} wf d) ss ag =
    relBindᵍ (subSem σS d ss ag) λ {v} {v′} sv → rel (
      ≈-TreeRelˡ (toT∞-fmap π (fromL σ F (ν F π)) (outν v))
        (≈-TreeRelʳ (toT∞-fmap π (fromL σ F (ν F π)) (outν v′))
          (treeFmap (outRel π (code (F ⟨ σ ⟩F)) sv)
                    (λ k → Functor.fromL-same σ r wf (ν F π) (LayerEq-∀ (code (F ⟨ σ ⟩F)) k)))))
  subSem σS (⊢iter {A = A} {B} df ds) ss ag =
    let (ss₁ , ag₁) = sr σS _ _ _ ss ag ; (ss₂ , ag₂) = sr σS _ _ _ ss ag in
    relBindᵍ (subSem σS df ss₁ ag₁) λ {f} {f′} sf →
    relBindᵍ (subSem σS ds ss₂ ag₂) λ sa →
    rel (Iter.iterRel (A ⟨ σ ⟩) (B ⟨ σ ⟩) f f′ (λ s → relPure⁻ (appMany sf s)) sa)
  subSem σS (⊢coerce p d) ss ag = relFmap (subSem σS d ss ag) (convSame σ p)
  subSem σS ⊢lit-int ss ag = relPure {A = Int} (λ n → refl)
  subSem σS ⊢lit-float ss ag = relPure {A = Float} (λ n → refl)
  subSem σS (⊢prim {π = π} p d) ss ag = relFmap {π} {π} (subSem σS d ss ag) (primSame σ p)
  subSem σS (⊢sigop {c = c₀} {t} mem) ss ag = relPure (sigopRefl σ c₀ t mem (interp δ))
  subSem σS (⊢sigop⁺ {c = c₀} {a} {q} {b = b} mem g) ss ag = relPure (sigop⁺Refl σ c₀ a q b mem g)
  subSem σS (⊢ref d τ rd) ss ag =
    relPure (substSame (sym (⟨⟩-∘ (type (S !! d)) τ σ))
                       (sd d (λ i → τ i ⟨ σ ⟩) (respects-∘ rd r) (respects-∘ rd r)))
  subSem σS (⊢sub-use p d) {γ} ss ag =
    subSem σS d (selfSame-restrict σ (·ᵐ-mono (usage σS) p) {γ = γ} ss) (subRestrict₁ σS (·ᵐ-mono (usage σS) p) p ag)
  subSem σS (⊢sub-eff g d) ss ag = relSubˡ g (relSubʳ g (subSem σS d ss ag))
