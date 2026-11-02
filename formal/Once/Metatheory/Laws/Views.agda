{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Views — what any derivation of a term former means,
-- in a restriction of the law's environment: its rule's clause, embedded in
-- `T∞` as a bind, its premises' environments again restrictions (`Res`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Views (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (Σ to Σ′)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; _·p_; positionGrade; mk-kind; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩; _*_; _+_; _⇒[_]_; Void)
open import Once.Spec.Context using (Ctx; ∅; []; _▸_; Usage; _∷_; _⊑ᵘ_; _⊑∷_; _+ᵘ_; _*ᵘ_; lookup; singleUse)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; toT∞; T∞; _≈_; _>>=∞_; return∞; bindᵍ; fmap)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Erase Σ using (toT∞-bindᵍ; toT∞-fmap; toT∞-bind)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; Related-trans; Related-flip; Related-mono; ≈-Relatedˡ; ≈-Relatedʳ; bindRel)
open import Once.Metatheory.Coherence.Layer Σ using (Rel; rel; runs; appMany)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Coherence.Env Σ fmt S
  using (SlotAgree; Agree; restrict-∘; restrictˡ; restrictʳ; selfAgree;
         envˡ-restrict; envʳ-restrict; env*One-restrict; env*Many-restrict)
open import Once.Metatheory.Coherence.Fundamental Σ u fmt S using (module FL)
open import Once.Metatheory.TermModel.Subst Σ S using (Thin; skip; keep; idθ; idθ-id; cid; cskip; ckeep; ren-⊢; θ*-id; ext-hρ; ⟦_⟧θ)
open import Once.Metatheory.TermModel.Ren Σ fmt S using (ThinAgree; module RenSem)
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-refl; ⊑ᵘ-trans; ⊑ᵘ-≡; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Metatheory.Laws.Strengthen Σ S using (str)
open import Once.Metatheory.TermModel.Val Σ fmt S using (At; NZ; nz-mono; nz-single; slotVal; val; restrict-val; lookup-val)
open import Once.Metatheory.Laws.Tools Σ u fmt S

-- Calling a function value of an arrow at quantity `q` (an erased argument is not passed).
callᵛ : ∀ (q : Quantity) {π} {A B : Type} → ⟦ A ⇒[ mk-kind q π ] B ⟧ᵛ → ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ
callᵛ Zero f a = f tt
callᵛ One  f a = f a
callᵛ Many f a = f a

module Views {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
             {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where

  private
    ag₀ : Agree σ Γ Ψ Ψ γ γ
    ag₀ = selfAgree σ Γ Ψ γ sγ

  -- A restriction of `γ` (`γ` itself is the one along `⊑ᵘ-refl`).
  data Res : ∀ {Ψa} → Env σ Γ Ψa → Set where
    res : ∀ {Ψa} (p : Ψa ⊑ᵘ Ψ) {γa} → γa ≡ restrict σ p γ → Res γa

  base : Res γ
  base = res (⊑ᵘ-refl Ψ) (sym (restrict-refl σ γ))

  agree : ∀ {Ψa Ψb} {γa : Env σ Γ Ψa} {γb : Env σ Γ Ψb} → Res γa → Res γb → Agree σ Γ Ψa Ψb γa γb
  agree (res p refl) (res p′ refl) = restrictˡ σ p (restrictʳ σ p′ ag₀)

  -- Forgetting more keeps an environment a restriction.
  resR : ∀ {Ψa Ψb} {γa : Env σ Γ Ψa} → Res γa → (p : Ψb ⊑ᵘ Ψa) → Res (restrict σ p γa)
  resR (res q refl) p = res (⊑ᵘ-trans p q) (restrict-∘ σ p q γ)

  private
    resEq : ∀ {Ψa} {x y : Env σ Γ Ψa} → x ≡ y → Res y → Res x
    resEq refl q = q

  resL : ∀ {Ψ₁ Ψ₂} {γa : Env σ Γ (Ψ₁ +ᵘ Ψ₂)} → Res γa → Res (envˡ σ Ψ₁ Ψ₂ γa)
  resL {Ψ₁} {Ψ₂} {γa} ra = resEq (envˡ-restrict σ Ψ₁ Ψ₂ γa) (resR ra (⊑ᵘ-+ˡ Ψ₁ Ψ₂))

  resRt : ∀ {Ψ₁ Ψ₂} {γa : Env σ Γ (Ψ₁ +ᵘ Ψ₂)} → Res γa → Res (envʳ σ Ψ₁ Ψ₂ γa)
  resRt {Ψ₁} {Ψ₂} {γa} ra = resEq (envʳ-restrict σ Ψ₁ Ψ₂ γa) (resR ra (⊑ᵘ-+ʳ Ψ₁ Ψ₂))

  res1 : ∀ {Ψ₁} {γa : Env σ Γ (One *ᵘ Ψ₁)} → Res γa → Res (env*One σ Ψ₁ γa)
  res1 {Ψ₁} {γa} ra = resEq (env*One-restrict σ Ψ₁ γa) (resR ra (⊑ᵘ-*One Ψ₁))

  resω : ∀ {Ψ₁} {γa : Env σ Γ (Many *ᵘ Ψ₁)} → Res γa → Res (env*Many σ Ψ₁ γa)
  resω {Ψ₁} {γa} ra = resEq (env*Many-restrict σ Ψ₁ γa) (resR ra (⊑ᵘ-*Many Ψ₁))

  -- A restriction's values are each the same as itself.
  sameEnvOf : ∀ {Ψa} {γa : Env σ Γ Ψa} → Res γa → SameEnv Σ fmt S σ Γ Ψa γa
  sameEnvOf ra = agreeSelf σ (agree ra ra)

  -- Two derivations of one term, in restrictions of `γ`: related.
  fl : ∀ {Ψa Ψb t A πa πb} (da : Δ ⊩ Γ ⊢[ Ψa ] t ∷ A ! πa) (db : Δ ⊩ Γ ⊢[ Ψb ] t ∷ A ! πb)
       {γa γb} → Res γa → Res γb → Rel πa πb (A ⟨ σ ⟩) (⟦ da ⟧ δ σ r γa) (⟦ db ⟧ δ σ r γb)
  fl da db ra rb = FL.FL δ sd σ r r da db refl (agree ra rb)

  -- The same, under one more binder whose values are the same.
  fl▸ : ∀ {Ψa Ψb qa qb B t A πa πb} (da : Δ ⊩ (Γ ▸ B) ⊢[ qa ∷ Ψa ] t ∷ A ! πa) (db : Δ ⊩ (Γ ▸ B) ⊢[ qb ∷ Ψb ] t ∷ A ! πb)
        {γa γb va vb} → Res γa → Res γb → SlotAgree σ B qa qb va vb
      → Rel πa πb (A ⟨ σ ⟩) (⟦ da ⟧ δ σ r (γa , va)) (⟦ db ⟧ δ σ r (γb , vb))
  fl▸ da db ra rb sv = FL.FL δ sd σ r r da db refl (agree ra rb , sv)

  -- A derivation means what the derivation under its sub-rules means.
  peelRel : ∀ {Ψa t A π} (d : Δ ⊩ Γ ⊢[ Ψa ] t ∷ A ! π) {γa} → Res γa
          → Rel π (Peeled.π₀ (peel d)) (A ⟨ σ ⟩) (⟦ d ⟧ δ σ r γa) (⟦ Peeled.D₀ (peel d) ⟧ δ σ r (restrict σ (Peeled.inc (peel d)) γa))
  peelRel d ra = fl d (Peeled.D₀ (peel d)) ra (resR ra (Peeled.inc (peel d)))

  -- Related computations, of a type.
  _~_ : ∀ {A : Ty m} → T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ → T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ → Set
  _~_ {A} = Related (Same (A ⟨ σ ⟩))

  ~trans : ∀ {A : Ty m} {x y z : T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ} → _~_ {A} x y → _~_ {A} y z → _~_ {A} x z
  ~trans {A} = Related-trans (Same-trans (A ⟨ σ ⟩))

  -- The meaning of a derivation, embedded.
  ⟪_⟫ : ∀ {Ψa t A π} → Δ ⊩ Γ ⊢[ Ψa ] t ∷ A ! π → Env σ Γ Ψa → T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ
  ⟪_⟫ {π = π} d γa = toT∞ π (⟦ d ⟧ δ σ r γa)

  ⟪_⟫▸ : ∀ {Ψa q B t A π} → Δ ⊩ (Γ ▸ B) ⊢[ q ∷ Ψa ] t ∷ A ! π → Env σ Γ Ψa → Slot q ⟦ B ⟨ σ ⟩ ⟧ᵛ → T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ
  ⟪_⟫▸ {π = π} d γa v = toT∞ π (⟦ d ⟧ δ σ r (γa , v))

  ----------------------------------------------------------------------
  -- inl, inr
  ----------------------------------------------------------------------

  record InlView {Ψa A B B′ πs a} (ds : Δ ⊩ Γ ⊢[ Ψa ] inl B a ∷ A + B′ ! πs) (γa : Env σ Γ Ψa) : Set where
    constructor inlView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      da   : Δ ⊩ Γ ⊢[ Ψ₀ ] a ∷ A ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {A + B′} (⟪ ds ⟫ γa) (⟪ da ⟫ γ₀ >>=∞ λ x → return∞ (inj₁ x))

  viewInl : ∀ {Ψa A B B′ πs a} (ds : Δ ⊩ Γ ⊢[ Ψa ] inl B a ∷ A + B′ ! πs) {γa} → Res γa → InlView ds γa
  viewInl ds ra with peel ds | peelRel ds ra
  ... | peeled (⊢inl {π = π₀} da) P _ | p =
    inlView da (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ inj₁ (⟦ da ⟧ δ σ r (restrict σ P _)))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  record InrView {Ψa A A′ B πs b} (ds : Δ ⊩ Γ ⊢[ Ψa ] inr A b ∷ A′ + B ! πs) (γa : Env σ Γ Ψa) : Set where
    constructor inrView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      db   : Δ ⊩ Γ ⊢[ Ψ₀ ] b ∷ B ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {A′ + B} (⟪ ds ⟫ γa) (⟪ db ⟫ γ₀ >>=∞ λ x → return∞ (inj₂ x))

  viewInr : ∀ {Ψa A A′ B πs b} (ds : Δ ⊩ Γ ⊢[ Ψa ] inr A b ∷ A′ + B ! πs) {γa} → Res γa → InrView ds γa
  viewInr ds ra with peel ds | peelRel ds ra
  ... | peeled (⊢inr {π = π₀} db) P _ | p =
    inrView db (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ inj₂ (⟦ db ⟧ δ σ r (restrict σ P _)))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  ----------------------------------------------------------------------
  -- case
  ----------------------------------------------------------------------

  record CaseView {Ψa qℓ qr C π s l rr} (d : Δ ⊩ Γ ⊢[ Ψa ] case qℓ qr s l rr ∷ C ! π) (γa : Env σ Γ Ψa) : Set where
    constructor caseView
    field
      {Ψs Ψc} : Usage n
      {π₁ π₂} : Purity
      {A B}   : Ty m
      ds      : Δ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁
      dl      : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψc ] l ∷ C ! π₂
      dr      : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψc ] rr ∷ C ! π₂
      {es ec} : Env σ Γ _
      rs      : Res {Ψs} es
      rc      : Res {Ψc} ec
      eq      : _~_ {C} (⟪ d ⟫ γa)
                  (⟪ ds ⟫ es >>=∞ [ (λ a → ⟪ dl ⟫▸ ec (slot qℓ a)) , (λ b → ⟪ dr ⟫▸ ec (slot qr b)) ]′)

  viewCase : ∀ {Ψa qℓ qr C π s l rr} (d : Δ ⊩ Γ ⊢[ Ψa ] case qℓ qr s l rr ∷ C ! π) {γa} → Res γa → CaseView d γa
  viewCase d ra with peel d | peelRel d ra
  ... | peeled (⊢case {Ψs = Ψs} {Ψc} {qℓ} {qr} {π₁} {π₂} ds dl dr) P _ | p =
    caseView ds dl dr (resL r₀) (resRt r₀)
      (≈-Relatedʳ (≈-trans (≈-bind (≈-refl _) λ { (inj₁ a) → ≈-refl _ ; (inj₂ b) → ≈-refl _ })
                           (≈-sym (toT∞-bindᵍ π₁ π₂ _ _)))
                  (runs p))
    where r₀ = resR ra P
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  ----------------------------------------------------------------------
  -- let
  ----------------------------------------------------------------------

  -- What a `let` at quantity `q` means: at `Zero` its right-hand side is not
  -- run; otherwise it runs, then the body with its value.
  LetSem : ∀ (q : Quantity) {Ψ₁ Ψ₂ A B π₁ π₂ e b} → T∞ ⟦ B ⟨ σ ⟩ ⟧ᵛ
         → Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁ → Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂ → Env σ Γ Ψ₂ → Set
  LetSem Zero {B = B} lhs de db eb = _~_ {B} lhs (⟪ db ⟫▸ eb tt)
  LetSem One  {Ψ₁} {B = B} lhs de db eb = Σ′ (Env σ Γ Ψ₁) λ ee → Res ee × _~_ {B} lhs (⟪ de ⟫ ee >>=∞ λ v → ⟪ db ⟫▸ eb v)
  LetSem Many {Ψ₁} {B = B} lhs de db eb = Σ′ (Env σ Γ Ψ₁) λ ee → Res ee × _~_ {B} lhs (⟪ de ⟫ ee >>=∞ λ v → ⟪ db ⟫▸ eb v)

  record LetView {Ψa q B π e b} (d : Δ ⊩ Γ ⊢[ Ψa ] let′ q e b ∷ B ! π) (γa : Env σ Γ Ψa) : Set where
    constructor letView
    field
      {Ψ₁ Ψ₂} : Usage n
      {π₁ π₂} : Purity
      {A}     : Ty m
      de      : Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁
      db      : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂
      {eb}    : Env σ Γ Ψ₂
      rb      : Res eb
      sem     : LetSem q (⟪ d ⟫ γa) de db eb

  viewLet : ∀ {Ψa q B π e b} (d : Δ ⊩ Γ ⊢[ Ψa ] let′ q e b ∷ B ! π) {γa} → Res γa → LetView d γa
  viewLet d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = Zero} {π₁} d₁ d₂) P _ | p =
    letView {π₁ = π₁} d₁ d₂ (resL (resR ra P)) (runs p)
  ... | peeled (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = One} {π₁} {π₂} d₁ d₂) P _ | p =
    letView d₁ d₂ (resL r₀) (ee , res1 (resRt r₀) ,
      ≈-Relatedʳ (≈-sym (toT∞-bindᵍ π₁ π₂ (⟦ d₁ ⟧ δ σ r ee) (λ v → ⟦ d₂ ⟧ δ σ r (envˡ σ Ψ₂ (One *ᵘ Ψ₁) γ₀ , v)))) (runs p))
    where γ₀ = restrict σ P γa
          r₀ = resR ra P
          ee = env*One σ Ψ₁ (envʳ σ Ψ₂ (One *ᵘ Ψ₁) γ₀)
  ... | peeled (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = Many} {π₁} {π₂} d₁ d₂) P _ | p =
    letView d₁ d₂ (resL r₀) (ee , resω (resRt r₀) ,
      ≈-Relatedʳ (≈-sym (toT∞-bindᵍ π₁ π₂ (⟦ d₁ ⟧ δ σ r ee) (λ v → ⟦ d₂ ⟧ δ σ r (envˡ σ Ψ₂ (Many *ᵘ Ψ₁) γ₀ , v)))) (runs p))
    where γ₀ = restrict σ P γa
          r₀ = resR ra P
          ee = env*Many σ Ψ₁ (envʳ σ Ψ₂ (Many *ᵘ Ψ₁) γ₀)
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  ----------------------------------------------------------------------
  -- Running `e`, then `b` with its value, is what `let′ q e b` means — at
  -- `Zero` because then `e` is effect-free (`transfer`)
  ----------------------------------------------------------------------

  ~sym : ∀ {A : Ty m} {x y : T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ} → _~_ {A} x y → _~_ {A} y x
  ~sym {A} p = Related-mono (Same-sym (A ⟨ σ ⟩)) (Related-flip p)

  letEnd : ∀ q {q′ Ψx ΨB Ψ₁ Ψ₂ A B πx πB π₁ π₂ e b} {lhs : T∞ ⟦ B ⟨ σ ⟩ ⟧ᵛ}
             (dx : Δ ⊩ Γ ⊢[ Ψx ] e ∷ A ! πx) {ex : Env σ Γ Ψx} → Res ex
         → (dB : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ ΨB ] b ∷ B ! πB) {eB : Env σ Γ ΨB} → Res eB
         → (de : Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁) (db : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂) {eb : Env σ Γ Ψ₂} → Res eb
         → LetSem q lhs de db eb
         → _~_ {B} (⟪ dx ⟫ ex >>=∞ λ x → ⟪ dB ⟫▸ eB (slot q′ x)) lhs
  letEnd Zero {q′} {A = A} {B} dx {ex} rx dB rB de db {eb} rb sem =
    ~trans {B} (≈-Relatedʳ (≈-sym (idˡ (⟦ px ⟧ δ σ r ex) (λ _ → ⟪ db ⟫▸ eb tt)))
                           (bindRel (runs (fl dx px rx rx)) (λ sv → runs (fl▸ dB db rB rb (slotAgree σ {A} q′ Zero sv)))))
               (~sym {B} sem)
    where px = transfer de dx
  letEnd One  {q′} {A = A} {B} dx rx dB rB de db rb (ee , re , eqR) =
    ~trans {B} (bindRel (runs (fl dx de rx re)) (λ sv → runs (fl▸ dB db rB rb (slotAgree σ {A} q′ One sv)))) (~sym {B} eqR)
  letEnd Many {q′} {A = A} {B} dx rx dB rB de db rb (ee , re , eqR) =
    ~trans {B} (bindRel (runs (fl dx de rx re)) (λ sv → runs (fl▸ dB db rB rb (slotAgree σ {A} q′ Many sv)))) (~sym {B} eqR)

  ----------------------------------------------------------------------
  -- var
  ----------------------------------------------------------------------

  record VarView {Ψa i π} (dv : Δ ⊩ Γ ⊢[ Ψa ] var i ∷ lookup Γ i ! π) (γa : Env σ Γ Ψa) : Set where
    constructor varView
    field
      P  : singleUse i One ⊑ᵘ Ψa
      eq : _~_ {lookup Γ i} (⟪ dv ⟫ γa) (return∞ (lookupᵛ σ Γ i (restrict σ P γa)))

  viewVar : ∀ {Ψa i π} (dv : Δ ⊩ Γ ⊢[ Ψa ] var i ∷ lookup Γ i ! π) {γa} → Res γa → VarView dv γa
  viewVar dv ra with peel dv | peelRel dv ra
  ... | peeled (⊢var i) P _ | p = varView P (runs p)
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  -- A variable, read in a restriction of `γ`, returns `γ`'s value.
  varVal : ∀ {Ψa i π} (dv : Δ ⊩ Γ ⊢[ Ψa ] var i ∷ lookup Γ i ! π) {γa} → Res γa
         → Σ′ (singleUse i One ⊑ᵘ Ψ) λ P₀ → _~_ {lookup Γ i} (⟪ dv ⟫ γa) (return∞ (lookupᵛ σ Γ i (restrict σ P₀ γ)))
  varVal dv (res Pv refl) with viewVar dv (res Pv refl)
  ... | varView P eq = ⊑ᵘ-trans P Pv , substR (restrict-∘ σ P Pv γ) eq
    where
      substR : ∀ {x y} → x ≡ y → _~_ {lookup Γ _} (⟪ dv ⟫ _) (return∞ (lookupᵛ σ Γ _ x))
             → _~_ {lookup Γ _} (⟪ dv ⟫ _) (return∞ (lookupᵛ σ Γ _ y))
      substR refl q = q

------------------------------------------------------------------------
-- Under a binder: `var zero` returns the bound value
------------------------------------------------------------------------

readVar0 : ∀ {m} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
             {n} {Γ : Ctx m n} {A : Ty m} {Ψ₂ q π₂} {eb : Env σ Γ Ψ₂} {v : ⟦ A ⟨ σ ⟩ ⟧ᵛ}
             (se : SameEnv Σ fmt S σ (Γ ▸ A) (q ∷ Ψ₂) (eb , slot q v))
             (db : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] var zero ∷ A ! π₂)
           → Related (Same (A ⟨ σ ⟩)) (toT∞ π₂ (⟦ db ⟧ δ σ r (eb , slot q v))) (return∞ v)
readVar0 δ sd σ r {Γ = Γ} {A} {Ψ₂} {q} {eb = eb} {v} se db = go (V.viewVar db V.base)
  where
    module V = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = q ∷ Ψ₂} (eb , slot q v) se
    go : V.VarView db (eb , slot q v) → Related (Same (A ⟨ σ ⟩)) (V.⟪ db ⟫ (eb , slot q v)) (return∞ v)
    go (V.varView (1≤1 ⊑∷ _) eq) = eq
    go (V.varView (1≤ω ⊑∷ _) eq) = eq

module AbsurdV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
               {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  record AbsurdView {Ψa A π e} (d : Δ ⊩ Γ ⊢[ Ψa ] absurd A e ∷ A ! π) (γa : Env σ Γ Ψa) : Set where
    constructor absurdView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      de   : Δ ⊩ Γ ⊢[ Ψ₀ ] e ∷ Void ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {A} (⟪ d ⟫ γa) (⟪ de ⟫ γ₀ >>=∞ λ ())

  viewAbsurd : ∀ {Ψa A π e} (d : Δ ⊩ Γ ⊢[ Ψa ] absurd A e ∷ A ! π) {γa} → Res γa → AbsurdView d γa
  viewAbsurd {A = A} d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢absurd {π = π₀} de) P _ | p =
    absurdView de (resR ra P)
      (≈-Relatedʳ (≈-trans (≈-bind (≈-refl _) λ ()) (≈-sym (toT∞-bind π₀ (⟦ de ⟧ δ σ r (restrict σ P γa)) ⊥-elim))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

module ProdV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
             {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  record PairView {Ψa A B π a b} (d : Δ ⊩ Γ ⊢[ Ψa ] pair a b ∷ A * B ! π) (γa : Env σ Γ Ψa) : Set where
    constructor pairView
    field
      {Ψ₁ Ψ₂} : Usage n
      {π₁ π₂} : Purity
      da      : Δ ⊩ Γ ⊢[ Ψ₁ ] a ∷ A ! π₁
      db      : Δ ⊩ Γ ⊢[ Ψ₂ ] b ∷ B ! π₂
      {ea}    : Env σ Γ Ψ₁
      {eb}    : Env σ Γ Ψ₂
      ra      : Res ea
      rb      : Res eb
      eq      : _~_ {A * B} (⟪ d ⟫ γa) (⟪ da ⟫ ea >>=∞ λ x → ⟪ db ⟫ eb >>=∞ λ y → return∞ (x , y))

  viewPair : ∀ {Ψa A B π a b} (d : Δ ⊩ Γ ⊢[ Ψa ] pair a b ∷ A * B ! π) {γa} → Res γa → PairView d γa
  viewPair d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} {π₁} {π₂} da db) P _ | p =
    pairView da db (resL r₀) (resRt r₀)
      (≈-Relatedʳ (≈-trans (≈-bind (≈-refl _) (λ x → ≈-sym (toT∞-fmap π₂ (λ y → x , y) (⟦ db ⟧ δ σ r eb))))
                           (≈-sym (toT∞-bindᵍ π₁ π₂ (⟦ da ⟧ δ σ r ea) (λ x → fmap π₂ (λ y → x , y) (⟦ db ⟧ δ σ r eb)))))
                  (runs p))
    where r₀ = resR ra P
          ea = envˡ σ Ψ₁ Ψ₂ (restrict σ P γa)
          eb = envʳ σ Ψ₁ Ψ₂ (restrict σ P γa)
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  record FstView {Ψa A π p} (d : Δ ⊩ Γ ⊢[ Ψa ] fst p ∷ A ! π) (γa : Env σ Γ Ψa) : Set where
    constructor fstView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      {B}  : Ty m
      dp   : Δ ⊩ Γ ⊢[ Ψ₀ ] p ∷ A * B ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {A} (⟪ d ⟫ γa) (⟪ dp ⟫ γ₀ >>=∞ λ v → return∞ (proj₁ v))

  viewFst : ∀ {Ψa A π p} (d : Δ ⊩ Γ ⊢[ Ψa ] fst p ∷ A ! π) {γa} → Res γa → FstView d γa
  viewFst d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢fst {π = π₀} dp) P _ | p =
    fstView dp (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ proj₁ (⟦ dp ⟧ δ σ r (restrict σ P γa)))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  record SndView {Ψa B π p} (d : Δ ⊩ Γ ⊢[ Ψa ] snd p ∷ B ! π) (γa : Env σ Γ Ψa) : Set where
    constructor sndView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      {A}  : Ty m
      dp   : Δ ⊩ Γ ⊢[ Ψ₀ ] p ∷ A * B ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {B} (⟪ d ⟫ γa) (⟪ dp ⟫ γ₀ >>=∞ λ v → return∞ (proj₂ v))

  viewSnd : ∀ {Ψa B π p} (d : Δ ⊩ Γ ⊢[ Ψa ] snd p ∷ B ! π) {γa} → Res γa → SndView d γa
  viewSnd d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢snd {π = π₀} dp) P _ | p =
    sndView dp (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ proj₂ (⟦ dp ⟧ δ σ r (restrict σ P γa)))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  -- An effect-free derivation returns: related to `return∞` of its value.
  pureRet : ∀ {Ψa Ψp t A π} (d : Δ ⊩ Γ ⊢[ Ψa ] t ∷ A ! π) (dp : Δ ⊩ Γ ⊢[ Ψp ] t ∷ A ! pure) {γa} (ra : Res γa)
          → _~_ {A} (⟪ d ⟫ γa) (return∞ (⟦ transfer dp d ⟧ δ σ r γa))
  pureRet d dp ra = runs (fl d (transfer dp d) ra ra)

------------------------------------------------------------------------
-- Weakening: `wk u` under a binder means what `u` means
------------------------------------------------------------------------

agree→thin : ∀ {m} (σ : TySub m 0) {n} (Γ : Ctx m n) {Ψ′ Ψ : Usage n} {γ′ : Env σ Γ Ψ′} {γ : Env σ Γ Ψ}
           → Agree σ Γ Ψ′ Ψ γ′ γ → ThinAgree σ (cid Γ) Ψ′ Ψ γ′ γ
agree→thin σ ∅       {[]}     {[]}     a        = tt
agree→thin σ (Γ ▸ A) {_ ∷ _}  {_ ∷ _}  (a , sv) = agree→thin σ Γ a , sv

module WkV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
           {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  wkRel : ∀ {A B q Ψ₂ Ψa π₂ πa t} (db : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] wk t ∷ B ! π₂) {eb : Env σ Γ Ψ₂} → Res eb
        → (v : Slot q ⟦ A ⟨ σ ⟩ ⟧ᵛ) (du : Δ ⊩ Γ ⊢[ Ψa ] t ∷ B ! πa) {γa : Env σ Γ Ψa} → Res γa
        → _~_ {B} (⟪ db ⟫▸ eb v) (⟪ du ⟫ γa)
  wkRel {A} {B} {q} {Ψa = Ψa} db {eb} rb v du {γa} ra =
    ~trans {B} (runs (FL.FL δ sd σ r r db D refl (agree rb rc , slotZ q v)))
               (runs (RenSem.renSem δ sd σ r (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip (cid Γ)) du
                        {γ′ = γc , tt} {γ = γa} (agree→thin σ Γ (agree rc ra))))
    where
      D = ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip {A = A} (cid Γ)) du
      W = ⊑ᵘ-≡ (θ*-id Ψa)
      γc = restrict σ W γa
      rc : Res γc
      rc = resR ra W
      slotZ : ∀ q (v : Slot q ⟦ A ⟨ σ ⟩ ⟧ᵛ) → SlotAgree σ A q Zero v tt
      slotZ Zero v = tt
      slotZ One  v = tt
      slotZ Many v = tt

module FunV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
            {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ
  open WkV δ sd σ r γ sγ using (wkRel)

  ----------------------------------------------------------------------
  -- lam: a value, whose calls run the body with the argument bound
  ----------------------------------------------------------------------

  record LamView {Ψa A q π′ T πd t} (d : Δ ⊩ Γ ⊢[ Ψa ] lam A q π′ t ∷ T ! πd) (γa : Env σ Γ Ψa) : Set where
    constructor lamView
    field
      {q′ Ψ₀} : _
      {B}     : Ty m
      le      : q′ ≤q q
      dt      : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ₀ ] t ∷ B ! π′
      {e₀}    : Env σ Γ Ψ₀
      r₀      : Res e₀
      eqT     : T ≡ (A ⇒[ mk-kind q π′ ] B)
      eq      : _~_ {T} (⟪ d ⟫ γa) (return∞ (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym eqT) (⟦ ⊢lam le dt ⟧ δ σ r e₀)))

  viewLam : ∀ {Ψa A q π′ T πd t} (d : Δ ⊩ Γ ⊢[ Ψa ] lam A q π′ t ∷ T ! πd) {γa} → Res γa → LamView d γa
  viewLam d ra with peel d | peelRel d ra
  ... | peeled (⊢lam le dt) P _ | p = lamView le dt (resR ra P) refl (runs p)
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  -- Calling the λ's value.
  lamCall : ∀ {A q′ q π′ B Ψ₀ t} (le : q′ ≤q q) (dt : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ₀ ] t ∷ B ! π′) (e₀ : Env σ Γ Ψ₀)
            (a : ⟦ A ⟨ σ ⟩ ⟧ᵛ)
          → callᵛ q (⟦ ⊢lam le dt ⟧ δ σ r e₀) a ≡ ⟦ dt ⟧ δ σ r (e₀ , slot q′ a)
  lamCall {q = Zero} 0≤q dt e₀ a = refl
  lamCall {q = One}  0≤q dt e₀ a = refl
  lamCall {q = Many} 0≤q dt e₀ a = refl
  lamCall 1≤1 dt e₀ a = refl
  lamCall 1≤ω dt e₀ a = refl
  lamCall ω≤ω dt e₀ a = refl

  ----------------------------------------------------------------------
  -- app: the function, then the argument (unless erased), then the call
  ----------------------------------------------------------------------

  AppSem : ∀ (q : Quantity) {Ψ₁ Ψ₂ A B π π₁ π₂ f x} → T∞ ⟦ B ⟨ σ ⟩ ⟧ᵛ
         → Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! π₁ → Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! positionGrade q π₂ → Env σ Γ Ψ₁ → Set
  AppSem Zero {B = B} {π = π} lhs df dx ef = _~_ {B} lhs (⟪ df ⟫ ef >>=∞ λ fv → toT∞ π (fv tt))
  AppSem One  {Ψ₂ = Ψ₂} {B = B} {π = π} lhs df dx ef =
    Σ′ (Env σ Γ Ψ₂) λ ex → Res ex × _~_ {B} lhs (⟪ df ⟫ ef >>=∞ λ fv → ⟪ dx ⟫ ex >>=∞ λ a → toT∞ π (fv a))
  AppSem Many {Ψ₂ = Ψ₂} {B = B} {π = π} lhs df dx ef =
    Σ′ (Env σ Γ Ψ₂) λ ex → Res ex × _~_ {B} lhs (⟪ df ⟫ ef >>=∞ λ fv → ⟪ dx ⟫ ex >>=∞ λ a → toT∞ π (fv a))

  record AppView {Ψa B π f x} (d : Δ ⊩ Γ ⊢[ Ψa ] app f x ∷ B ! π) (γa : Env σ Γ Ψa) : Set where
    constructor appView
    field
      {Ψ₁ Ψ₂}  : Usage n
      {q}      : Quantity
      {πl π₁ π₂} : Purity
      {A}      : Ty m
      df       : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q πl ] B ! π₁
      dx       : Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! positionGrade q π₂
      {ef}     : Env σ Γ Ψ₁
      rf       : Res ef
      sem      : AppSem q (⟪ d ⟫ γa) df dx ef

  viewApp : ∀ {Ψa B π f x} (d : Δ ⊩ Γ ⊢[ Ψa ] app f x ∷ B ! π) {γa} → Res γa → AppView d γa
  viewApp d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = Zero} {πl} {π₁} {π₂} df dx) P _ | p =
    appView {π₂ = π₂} df dx (resL (resR ra P))
      (≈-Relatedʳ (≈-sym (toT∞-bindᵍ π₁ πl (⟦ df ⟧ δ σ r (envˡ σ Ψ₁ (Zero *ᵘ Ψ₂) γ₀)) (λ fv → fv tt))) (runs p))
    where γ₀ = restrict σ P γa
  ... | peeled (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = One} {πl} {π₁} {π₂} df dx) P _ | p =
    appView df dx (resL r₀) (ex , res1 (resRt r₀) ,
      ≈-Relatedʳ (≈-trans (≈-bind (≈-refl _) λ fv → ≈-sym (toT∞-bindᵍ π₂ πl (⟦ dx ⟧ δ σ r ex) fv))
                          (≈-sym (toT∞-bindᵍ π₁ (π₂ ·p πl) (⟦ df ⟧ δ σ r (envˡ σ Ψ₁ (One *ᵘ Ψ₂) γ₀))
                                    (λ fv → bindᵍ π₂ πl (⟦ dx ⟧ δ σ r ex) fv))))
                 (runs p))
    where γ₀ = restrict σ P γa
          r₀ = resR ra P
          ex = env*One σ Ψ₂ (envʳ σ Ψ₁ (One *ᵘ Ψ₂) γ₀)
  ... | peeled (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = Many} {πl} {π₁} {π₂} df dx) P _ | p =
    appView df dx (resL r₀) (ex , resω (resRt r₀) ,
      ≈-Relatedʳ (≈-trans (≈-bind (≈-refl _) λ fv → ≈-sym (toT∞-bindᵍ π₂ πl (⟦ dx ⟧ δ σ r ex) fv))
                          (≈-sym (toT∞-bindᵍ π₁ (π₂ ·p πl) (⟦ df ⟧ δ σ r (envˡ σ Ψ₁ (Many *ᵘ Ψ₂) γ₀))
                                    (λ fv → bindᵍ π₂ πl (⟦ dx ⟧ δ σ r ex) fv))))
                 (runs p))
    where γ₀ = restrict σ P γa
          r₀ = resR ra P
          ex = env*Many σ Ψ₂ (envʳ σ Ψ₁ (Many *ᵘ Ψ₂) γ₀)
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  -- An application at a `Many` arrow, the function's value known: the argument, then the call.
  appMany~ : ∀ {Ψ₁ Ψ₂ A B π π₁ π₂ f x ef} {lhs : T∞ ⟦ B ⟨ σ ⟩ ⟧ᵛ} {fv′ : ⟦ (A ⇒[ mk-kind Many π ] B) ⟨ σ ⟩ ⟧ᵛ} {X : T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ}
             (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! π₁) (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! π₂)
           → AppSem Many lhs df dx ef
           → _~_ {A ⇒[ mk-kind Many π ] B} (⟪ df ⟫ ef) (return∞ fv′)
           → (∀ {ex} → Res ex → _~_ {A} (⟪ dx ⟫ ex) X)
           → _~_ {B} lhs (X >>=∞ λ a → toT∞ π (fv′ a))
  appMany~ {A = A} {B} {π} {fv′ = fv′} {X} df dx (ex , rx , eqA) rf hx =
    ~trans {B} eqA (≈-Relatedʳ (≈-sym (idˡ fv′ K′))
      (bindRel {f = λ h → ⟪ dx ⟫ ex >>=∞ λ a → toT∞ π (h a)} {g = K′} rf
        (λ {h} {h′} sh → bindRel {f = λ a → toT∞ π (h a)} {g = λ a → toT∞ π (h′ a)} (hx rx)
           (λ sa → runs (appMany {π} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sh sa)))))
    where K′ : _ → T∞ _
          K′ h = X >>=∞ λ a → toT∞ π (h a)

  -- `wk t`, run in a restriction of an environment one binder longer.
  wkRelR : ∀ {A B q q′ Ψ₀ Ψ₁ Ψa π₁ πa t} (db : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₁ ] wk t ∷ B ! π₁) {e₀ : Env σ Γ Ψ₀} → Res e₀
         → (w : Slot q′ ⟦ A ⟨ σ ⟩ ⟧ᵛ) (Pf : (q ∷ Ψ₁) ⊑ᵘ (q′ ∷ Ψ₀))
         → (du : Δ ⊩ Γ ⊢[ Ψa ] t ∷ B ! πa) {γa : Env σ Γ Ψa} → Res γa
         → _~_ {B} (toT∞ π₁ (⟦ db ⟧ δ σ r (restrict σ {Γ = Γ ▸ A} Pf (e₀ , w)))) (⟪ du ⟫ γa)
  wkRelR {A} {B} db r₀ w (0≤q ⊑∷ Ps) du ra = wkRel {A} {B} db (resR r₀ Ps) tt du ra
  wkRelR {A} {B} db r₀ w (1≤1 ⊑∷ Ps) du ra = wkRel {A} {B} db (resR r₀ Ps) w du ra
  wkRelR {A} {B} db r₀ w (1≤ω ⊑∷ Ps) du ra = wkRel {A} {B} db (resR r₀ Ps) w du ra
  wkRelR {A} {B} db r₀ w (ω≤ω ⊑∷ Ps) du ra = wkRel {A} {B} db (resR r₀ Ps) w du ra

------------------------------------------------------------------------
-- Environments one binder longer: agreement with a restriction of one
------------------------------------------------------------------------

module ExtV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
            {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  agreeExtR : ∀ {A q₁ q q₂ Ψ₁ Ψp Ψ₂} {e₁ : Env σ Γ Ψ₁} {e₂ : Env σ Γ Ψ₂} → Res e₁ → Res e₂
            → ∀ {a a′} → Same (A ⟨ σ ⟩) a a′ → (P : (q ∷ Ψp) ⊑ᵘ (q₂ ∷ Ψ₂))
            → Agree σ (Γ ▸ A) (q₁ ∷ Ψ₁) (q ∷ Ψp) (e₁ , slot q₁ a) (restrict σ {Γ = Γ ▸ A} P (e₂ , slot q₂ a′))
  agreeExtR {A} {q₁} r₁ r₂ sa (0≤q ⊑∷ Ps) = agree r₁ (resR r₂ Ps) , slotAgree σ {A} q₁ Zero sa
  agreeExtR {A} {q₁} r₁ r₂ sa (1≤1 ⊑∷ Ps) = agree r₁ (resR r₂ Ps) , slotAgree σ {A} q₁ One sa
  agreeExtR {A} {q₁} r₁ r₂ sa (1≤ω ⊑∷ Ps) = agree r₁ (resR r₂ Ps) , slotAgree σ {A} q₁ One sa
  agreeExtR {A} {q₁} r₁ r₂ sa (ω≤ω ⊑∷ Ps) = agree r₁ (resR r₂ Ps) , slotAgree σ {A} q₁ Many sa

  -- against an environment whose new variable is unused
  agreeExtZ : ∀ {A q q₂ Ψp Ψ₂ Ψ₃} {e₂ : Env σ Γ Ψ₂} {e₃ : Env σ Γ Ψ₃} → Res e₂ → Res e₃
            → (w : Slot q₂ ⟦ A ⟨ σ ⟩ ⟧ᵛ) (P : (q ∷ Ψp) ⊑ᵘ (q₂ ∷ Ψ₂))
            → Agree σ (Γ ▸ A) (q ∷ Ψp) (Zero ∷ Ψ₃) (restrict σ {Γ = Γ ▸ A} P (e₂ , w)) (e₃ , tt)
  agreeExtZ r₂ r₃ w (0≤q ⊑∷ Ps) = agree (resR r₂ Ps) r₃ , tt
  agreeExtZ r₂ r₃ w (1≤1 ⊑∷ Ps) = agree (resR r₂ Ps) r₃ , tt
  agreeExtZ r₂ r₃ w (1≤ω ⊑∷ Ps) = agree (resR r₂ Ps) r₃ , tt
  agreeExtZ r₂ r₃ w (ω≤ω ⊑∷ Ps) = agree (resR r₂ Ps) r₃ , tt

  -- `ren (ext suc) v` (one binder inserted under the first) means what `v` means.
  renUp : ∀ {A C D q q″ q₀ q₂ Ψb Ψp Ψ₂ πb π″ v} (db : Δ ⊩ (Γ ▸ C) ⊢[ q ∷ Ψb ] v ∷ D ! πb) {eb : Env σ Γ Ψb} → Res eb
        → (y : Slot q ⟦ C ⟨ σ ⟩ ⟧ᵛ) → SlotAgree σ C q q y y
        → (db″ : Δ ⊩ (Γ ▸ A ▸ C) ⊢[ q″ ∷ q₀ ∷ Ψp ] ren (ext {S = S} {m = m} suc) v ∷ D ! π″) {e₂ : Env σ Γ Ψ₂} → Res e₂
        → (w : Slot q₂ ⟦ A ⟨ σ ⟩ ⟧ᵛ) (P₂ : (q₀ ∷ Ψp) ⊑ᵘ (q₂ ∷ Ψ₂)) (y″ : Slot q″ ⟦ C ⟨ σ ⟩ ⟧ᵛ) → SlotAgree σ C q″ q y″ y
        → _~_ {D} (toT∞ π″ (⟦ db″ ⟧ δ σ r (restrict σ {Γ = Γ ▸ A} P₂ (e₂ , w) , y″))) (⟪ db ⟫▸ eb y)
  renUp {A} {C} {D} {q} {Ψb = Ψb} db {eb} rb y sy db″ r₂ w P₂ y″ s″ =
    ~trans {D} (runs (FL.FL δ sd σ r r db″ R refl (agreeExtZ r₂ (resR rb W) w P₂ , s″)))
               (runs (RenSem.renSem δ sd σ r (keep (skip (idθ n))) (ext {S = S} {m = m} suc) (ext-hρ {m = m} (skip (idθ n)) suc h₀)
                        (ckeep (cskip {A = A} (cid Γ))) db {γ′ = (restrict σ W eb , tt) , y} {γ = eb , y}
                        (agree→thin σ Γ (agree (resR rb W) rb) , sy)))
    where
      h₀ : ∀ (i : Fin n) → ⟦ skip (idθ n) ⟧θ i ≡ suc i
      h₀ i = cong suc (idθ-id i)
      W = ⊑ᵘ-≡ (θ*-id Ψb)
      R = ren-⊢ (keep (skip (idθ n))) (ext {S = S} {m = m} suc) (ext-hρ {m = m} (skip (idθ n)) suc h₀) (ckeep (cskip {A = A} (cid Γ))) db

  -- the same, for slots related at any quantities
  agreeExtS : ∀ {A q₁ q q₂ Ψ₁ Ψp Ψ₂} {e₁ : Env σ Γ Ψ₁} {e₂ : Env σ Γ Ψ₂} → Res e₁ → Res e₂
            → ∀ {w₁ w₂} → SlotAgree σ A q₁ q₂ w₁ w₂ → (P : (q ∷ Ψp) ⊑ᵘ (q₂ ∷ Ψ₂))
            → Agree σ (Γ ▸ A) (q₁ ∷ Ψ₁) (q ∷ Ψp) (e₁ , w₁) (restrict σ {Γ = Γ ▸ A} P (e₂ , w₂))
  agreeExtS {A} {q₁} r₁ r₂ sw (0≤q ⊑∷ Ps) = agree r₁ (resR r₂ Ps) , z q₁
    where z : ∀ q₁ {w} → SlotAgree σ A q₁ Zero w tt
          z Zero = tt
          z One  = tt
          z Many = tt
  agreeExtS r₁ r₂ sw (1≤1 ⊑∷ Ps) = agree r₁ (resR r₂ Ps) , sw
  agreeExtS {A} {q₁} r₁ r₂ sw (1≤ω ⊑∷ Ps) = agree r₁ (resR r₂ Ps) , m→1 q₁ sw
    where m→1 : ∀ q₁ {w₁ w₂} → SlotAgree σ A q₁ Many w₁ w₂ → SlotAgree σ A q₁ One w₁ w₂
          m→1 Zero s = tt
          m→1 One  s = s
          m→1 Many s = s
  agreeExtS r₁ r₂ sw (ω≤ω ⊑∷ Ps) = agree r₁ (resR r₂ Ps) , sw

------------------------------------------------------------------------
-- Reading variables by `val` (`TermModel.Val`): through restrictions, and
-- the value a slot was filled with
------------------------------------------------------------------------

module ReadV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
             {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  readV : ∀ {Ψa i π} (dv : Δ ⊩ Γ ⊢[ Ψa ] var i ∷ lookup Γ i ! π) {γa} → Res γa
        → Σ′ (NZ (At Ψ i)) λ nz → _~_ {lookup Γ i} (⟪ dv ⟫ γa) (return∞ (val σ γ i nz))
  readV {i = i} dv ra with varVal dv ra
  ... | P₀ , eq = nz-mono P₀ i (nz-single i) , substR (trans (lookup-val σ Γ i (restrict σ P₀ γ)) (restrict-val σ P₀ γ i (nz-single i))) eq
    where
      substR : ∀ {x y} → x ≡ y → _~_ {lookup Γ i} (⟪ dv ⟫ _) (return∞ x) → _~_ {lookup Γ i} (⟪ dv ⟫ _) (return∞ y)
      substR refl q = q

slotVal∘slot : ∀ {m} (σ : TySub m 0) q {X : Set} (x : X) (nz : NZ q) → slotVal σ q (slot q x) nz ≡ x
slotVal∘slot σ One  x nz = refl
slotVal∘slot σ Many x nz = refl

------------------------------------------------------------------------
-- The arms of a combinator: `let′ One e (let′ q (wk e₂) b)`, both read in Γ
------------------------------------------------------------------------

module ArmsV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
             {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  record Arms {Ψa T π₀ t} (d : Δ ⊩ Γ ⊢[ Ψa ] t ∷ T ! π₀) (e e₂ : Tm S m n) : Set where
    constructor arms
    field
      {Ψe Ψg} : Usage n
      {πe πg} : Purity
      {E G}   : Ty m
      de      : Δ ⊩ Γ ⊢[ Ψe ] e ∷ E ! πe
      dg      : Δ ⊩ Γ ⊢[ Ψg ] e₂ ∷ G ! πg
      Pe      : Ψe ⊑ᵘ Ψa
      Pg      : Ψg ⊑ᵘ Ψa

  armsLL : ∀ {Ψa T π₀ q e e₂ b} → (q ≡ One ⊎ q ≡ Many)
         → (d : Δ ⊩ Γ ⊢[ Ψa ] let′ One e (let′ q (wk e₂) b) ∷ T ! π₀) → Arms d e e₂
  armsLL {q = q} nz d with peel d
  ... | peeled (⊢let {Ψ₁ = Ψe} {Ψ₂ = Ψb} de db) P _ with peel db
  ...   | peeled (⊢let {Ψ₁ = qw ∷ Ψw} {Ψ₂ = ql ∷ Ψl} dw _) (_ ⊑∷ P′) _ =
          arms de (str dw) (⊑ᵘ-trans (⊑ᵘ-trans (⊑ᵘ-*One Ψe) (⊑ᵘ-+ʳ Ψb (One *ᵘ Ψe))) P)
                           (⊑ᵘ-trans (⊑ᵘ-trans (⊑ᵘ-trans (scale nz Ψw) (⊑ᵘ-+ʳ Ψl (q *ᵘ Ψw))) P′)
                                     (⊑ᵘ-trans (⊑ᵘ-+ˡ Ψb (One *ᵘ Ψe)) P))
    where
      scale : (q ≡ One ⊎ q ≡ Many) → ∀ Ψw → Ψw ⊑ᵘ q *ᵘ Ψw
      scale (inj₁ refl) Ψw = ⊑ᵘ-*One Ψw
      scale (inj₂ refl) Ψw = ⊑ᵘ-*Many Ψw
  ...   | peeled (⊢sub-use _ _) _ ()
  ...   | peeled (⊢sub-eff _ _) _ ()
  armsLL nz d | peeled (⊢sub-use _ _) _ ()
  armsLL nz d | peeled (⊢sub-eff _ _) _ ()

  record Arm1 {Ψa T π₀ t} (d : Δ ⊩ Γ ⊢[ Ψa ] t ∷ T ! π₀) (e : Tm S m n) : Set where
    constructor arm1
    field
      {Ψe} : Usage n
      {πe} : Purity
      {E}  : Ty m
      de   : Δ ⊩ Γ ⊢[ Ψe ] e ∷ E ! πe
      Pe   : Ψe ⊑ᵘ Ψa

  armL1 : ∀ {Ψa T π₀ e b} (d : Δ ⊩ Γ ⊢[ Ψa ] let′ One e b ∷ T ! π₀) → Arm1 d e
  armL1 d with peel d
  ... | peeled (⊢let {Ψ₁ = Ψe} {Ψ₂ = Ψb} de _) P _ = arm1 de (⊑ᵘ-trans (⊑ᵘ-trans (⊑ᵘ-*One Ψe) (⊑ᵘ-+ʳ Ψb (One *ᵘ Ψe))) P)
  ... | peeled (⊢sub-use _ _) _ ()
  ... | peeled (⊢sub-eff _ _) _ ()
