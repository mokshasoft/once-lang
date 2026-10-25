-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecRenameSem — the Spec's core meaning is STABLE UNDER
-- RENAMING, on the nose (plan 0.103 6b step B.1; plan 0.122 §5.5 M4: over the
-- Spec's meaning).
--
--   ⟦ ren-⊢ θ ρ h c d ⟧ δ σ r x ≡ ⟦ d ⟧ δ σ r (thinᴱ c Ψ x)
--
-- The derived combinators weaken an arm (`wk-⊢`), so the surface bridge
-- (surface meaning = core meaning of the elaboration) needs to know what
-- renaming MEANS. The meaning runs over the environment of the variables a
-- term uses; `ren-⊢` moves a usage by a cast (a restriction), and each rule
-- splits its environment by `envˡ`/`envʳ`/`env*One`/`env*Many`, which are
-- restrictions too (`Coherence.Env`). So besides the environment thinning
-- `thinᴱ` the proof needs: `_⊑ᵘ_` is proof-irrelevant, restrictions compose,
-- and restriction commutes with `thinᴱ`. (The term model's own renaming lemma,
-- `Metatheory.TermModel.Ren`, is relational; the compiler needs it on the
-- nose.)
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecRenameSem (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Once.Postulates using (extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; eff; fin; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩)
open import Once.Spec.Context using (Ctx; ∅; _▸_; Usage; []; _∷_; _⊑∷_; _⊑ᵘ_; singleUse; lookup)
open import Once.Internal.Context using (⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; ⊑ᵘ-unique)
open import Once.Spec.Context using (_*ᵘ_; _+ᵘ_)
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SD
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.TermModel.Subst Σ S
  using (Thin; done; keep; skip; ⟦_⟧θ; _θ*_; θ*-mono; idθ; idθ-id; CThin; cdone; ckeep; cskip; cid; cthin-lookup;
         θ*-id; retype; varAt; ren-⊢; wk-⊢)
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-≡)
open import Once.Spec.Core.Meaning Σ fmt S using (⟦_⟧; DefSem; Env; restrict; envˡ; envʳ; env*One; env*Many; lookupᵛ; slot)
open import Once.Metatheory.Coherence.Env Σ fmt S
  using (envˡ-restrict; envʳ-restrict; env*One-envʳ-restrict; env*Many-envʳ-restrict; env*Many-envˡ-restrict)

module _ (σ : TySub 0 0) where

  ------------------------------------------------------------------------
  -- Restrictions: proof-irrelevant, and they compose
  ------------------------------------------------------------------------

  restrict-∘ : ∀ {n} {Γ : Ctx 0 n} {Ψ₀ Ψ₁ Ψ₂ : Usage n} (u : Ψ₀ ⊑ᵘ Ψ₁) (v : Ψ₁ ⊑ᵘ Ψ₂) (x : Env σ Γ Ψ₂)
             → restrict σ u (restrict σ v x) ≡ restrict σ (⊑ᵘ-trans u v) x
  restrict-∘ {Γ = ∅}     []          []          x       = refl
  restrict-∘ {Γ = Γ ▸ A} (0≤q ⊑∷ u) (0≤q ⊑∷ v) (x , a) = cong (_, tt) (restrict-∘ u v x)
  restrict-∘ {Γ = Γ ▸ A} (0≤q ⊑∷ u) (1≤1 ⊑∷ v) (x , a) = cong (_, tt) (restrict-∘ u v x)
  restrict-∘ {Γ = Γ ▸ A} (0≤q ⊑∷ u) (1≤ω ⊑∷ v) (x , a) = cong (_, tt) (restrict-∘ u v x)
  restrict-∘ {Γ = Γ ▸ A} (0≤q ⊑∷ u) (ω≤ω ⊑∷ v) (x , a) = cong (_, tt) (restrict-∘ u v x)
  restrict-∘ {Γ = Γ ▸ A} (1≤1 ⊑∷ u) (1≤1 ⊑∷ v) (x , a) = cong (_, a) (restrict-∘ u v x)
  restrict-∘ {Γ = Γ ▸ A} (1≤1 ⊑∷ u) (1≤ω ⊑∷ v) (x , a) = cong (_, a) (restrict-∘ u v x)
  restrict-∘ {Γ = Γ ▸ A} (1≤ω ⊑∷ u) (ω≤ω ⊑∷ v) (x , a) = cong (_, a) (restrict-∘ u v x)
  restrict-∘ {Γ = Γ ▸ A} (ω≤ω ⊑∷ u) (ω≤ω ⊑∷ v) (x , a) = cong (_, a) (restrict-∘ u v x)

  restrict-irr : ∀ {n} {Γ : Ctx 0 n} {Ψ Ψ′ : Usage n} (u v : Ψ′ ⊑ᵘ Ψ) (x : Env σ Γ Ψ) → restrict σ u x ≡ restrict σ v x
  restrict-irr u v x = cong (λ w → restrict σ w x) (⊑ᵘ-unique u v)

  ------------------------------------------------------------------------
  -- The environment a thinning induces
  ------------------------------------------------------------------------

  -- `skip` drops the slot the thinning added; `keep` keeps its slot.
  thinᴱ : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) (Ψ : Usage n)
        → Env σ Γ′ (θ θ* Ψ) → Env σ Γ Ψ
  thinᴱ cdone     []      x       = x
  thinᴱ (cskip c) Ψ       (x , _) = thinᴱ c Ψ x
  thinᴱ (ckeep c) (q ∷ Ψ) (x , v) = thinᴱ c Ψ x , v

  -- Thinning and restriction commute.
  thin-restrict : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) {Ψ′ Ψ : Usage n}
                  (u : Ψ′ ⊑ᵘ Ψ) (x : Env σ Γ′ (θ θ* Ψ))
                → thinᴱ c Ψ′ (restrict σ (θ*-mono θ u) x) ≡ restrict σ u (thinᴱ c Ψ x)
  thin-restrict cdone     []          x       = refl
  thin-restrict (cskip c) u           (x , _) = thin-restrict c u x
  thin-restrict (ckeep c) (0≤q ⊑∷ u) (x , _) = cong (_, tt) (thin-restrict c u x)
  thin-restrict (ckeep c) (1≤1 ⊑∷ u) (x , a) = cong (_, a) (thin-restrict c u x)
  thin-restrict (ckeep c) (1≤ω ⊑∷ u) (x , a) = cong (_, a) (thin-restrict c u x)
  thin-restrict (ckeep c) (ω≤ω ⊑∷ u) (x , a) = cong (_, a) (thin-restrict c u x)

  -- The environment of a subterm: two restrictions (the cast `ren-⊢` puts on a
  -- rule, then the rule's own split), thinned, are the split of the thinned one.
  envEq : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) {Ψ′ Ψ : Usage n} {U : Usage n′}
            (u : Ψ′ ⊑ᵘ Ψ) (u₁ : θ θ* Ψ′ ⊑ᵘ U) (u₂ : U ⊑ᵘ θ θ* Ψ) (x : Env σ Γ′ (θ θ* Ψ))
        → thinᴱ c Ψ′ (restrict σ u₁ (restrict σ u₂ x)) ≡ restrict σ u (thinᴱ c Ψ x)
  envEq {θ = θ} c {Ψ′} u u₁ u₂ x =
    trans (cong (thinᴱ c Ψ′) (trans (restrict-∘ u₁ u₂ x) (restrict-irr (⊑ᵘ-trans u₁ u₂) (θ*-mono θ u) x)))
          (thin-restrict c u x)

  -- A rule's split, after the cast, thinned: the thinned split. `f` and `g` are
  -- the rule's split on either side, each a restriction.
  split : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) {Ψ′ Ψ : Usage n} {U : Usage n′}
            (f : Env σ Γ′ U → Env σ Γ′ (θ θ* Ψ′)) (g : Env σ Γ Ψ → Env σ Γ Ψ′)
            (u₁ : θ θ* Ψ′ ⊑ᵘ U) (u : Ψ′ ⊑ᵘ Ψ)
          → (∀ y → f y ≡ restrict σ u₁ y) → (∀ z → g z ≡ restrict σ u z)
          → (u₂ : U ⊑ᵘ θ θ* Ψ) (x : Env σ Γ′ (θ θ* Ψ))
          → thinᴱ c Ψ′ (f (restrict σ u₂ x)) ≡ g (thinᴱ c Ψ x)
  split c {Ψ′} f g u₁ u ef eg u₂ x =
    trans (cong (thinᴱ c Ψ′) (ef _)) (trans (envEq c u u₁ u₂ x) (sym (eg _)))

  -- The variable: thinning preserves lookup.
  lookup-thin : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) (i : Fin n)
                  (u : singleUse (⟦ θ ⟧θ i) One ⊑ᵘ θ θ* singleUse i One) (x : Env σ Γ′ (θ θ* singleUse i One))
              → subst (λ X → SD.⟦ X ⟨ σ ⟩ ⟧ᵛ) (cthin-lookup c i) (lookupᵛ σ Γ′ (⟦ θ ⟧θ i) (restrict σ u x))
                ≡ lookupᵛ σ Γ i (thinᴱ c (singleUse i One) x)
  lookup-thin (cskip c) i       (0≤q ⊑∷ u) (x , _) = lookup-thin c i u x
  lookup-thin (ckeep c) zero    (1≤1 ⊑∷ u) (x , a) = refl
  lookup-thin (ckeep c) (suc i) (0≤q ⊑∷ u) (x , _) = lookup-thin c i u x

  -- The identity thinning, after a restriction onto its usage, is the identity.
  thin-id : ∀ {n} (Γ : Ctx 0 n) (Ψ : Usage n) (v : idθ n θ* Ψ ⊑ᵘ Ψ) (x : Env σ Γ Ψ)
          → thinᴱ (cid Γ) Ψ (restrict σ v x) ≡ x
  thin-id ∅       []         []          x       = refl
  thin-id (Γ ▸ A) (Zero ∷ Ψ) (0≤q ⊑∷ v) (x , tt) = cong (_, tt) (thin-id Γ Ψ v x)
  thin-id (Γ ▸ A) (One  ∷ Ψ) (1≤1 ⊑∷ v) (x , a)  = cong (_, a) (thin-id Γ Ψ v x)
  thin-id (Γ ▸ A) (Many ∷ Ψ) (ω≤ω ⊑∷ v) (x , a)  = cong (_, a) (thin-id Γ Ψ v x)

  ------------------------------------------------------------------------
  -- THE RENAMING LEMMA
  ------------------------------------------------------------------------

  module _ {Δ : KCtx 0} (δ : DefSem) (r : Respects Δ ∅ₖ σ) where

    private
      ⟦⟧ : ∀ {n} {Γ : Ctx 0 n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Env σ Γ Ψ → SE.M π SD.⟦ A ⟨ σ ⟩ ⟧ᵛ
      ⟦⟧ d = ⟦ d ⟧ δ σ r

      bindCᵍ : ∀ {π₁ π₂} {X Y : Set} {a a′ : SE.M π₁ X} {f g : X → SE.M π₂ Y} → a ≡ a′ → (∀ v → f v ≡ g v)
             → SE.bindᵍ π₁ π₂ a f ≡ SE.bindᵍ π₁ π₂ a′ g
      bindCᵍ {π₁} {π₂} {a = a} refl h = cong (SE.bindᵍ π₁ π₂ a) (extensionality h)

      bindC : ∀ {π} {X Y : Set} {a a′ : SE.M π X} {f g : X → SE.M π Y} → a ≡ a′ → (∀ v → f v ≡ g v) → SE.bind π a f ≡ SE.bind π a′ g
      bindC {π} {a = a} refl h = cong (SE.bind π a) (extensionality h)

    -- A retyped derivation means the transported meaning.
    ⟦⟧-retype : ∀ {n} {Γ : Ctx 0 n} {Ψ t A A′ π} (e : A ≡ A′) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (x : Env σ Γ Ψ)
              → ⟦⟧ (retype e d) x ≡ subst (λ X → SE.M π SD.⟦ X ⟨ σ ⟩ ⟧ᵛ) e (⟦⟧ d x)
    ⟦⟧-retype refl d x = refl

    var-sem : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) (i : Fin n) {j} (e : ⟦ θ ⟧θ i ≡ j)
                (x : Env σ Γ′ (θ θ* singleUse i One))
            → ⟦⟧ (varAt {Δ = Δ} c i e) x ≡ lookupᵛ σ Γ i (thinᴱ c (singleUse i One) x)
    var-sem {θ = θ} c i refl x =
      trans (⟦⟧-retype (cthin-lookup c i) (⊢var (⟦ θ ⟧θ i)) _) (lookup-thin c i _ x)

    ren-sem : ∀ {n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) (h : ∀ i → ⟦ θ ⟧θ i ≡ ρ i)
                {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) {Ψ t A π} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
                (x : Env σ Γ′ (θ θ* Ψ))
            → ⟦⟧ (ren-⊢ θ ρ h c d) x ≡ ⟦⟧ d (thinᴱ c Ψ x)

    ren-sem θ ρ h c (⊢var i) x = var-sem c i (h i) x

    ren-sem θ ρ h c (⊢lam {q = Zero} 0≤q d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
    ren-sem θ ρ h c (⊢lam {q = One}  0≤q d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
    ren-sem θ ρ h c (⊢lam {q = Many} 0≤q d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
    ren-sem θ ρ h c (⊢lam 1≤1 d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
    ren-sem θ ρ h c (⊢lam 1≤ω d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
    ren-sem θ ρ h c (⊢lam ω≤ω d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _

    ren-sem θ ρ h c (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {π = π} {π₁ = π₁} df dx) x =
      bindCᵍ {π₁} {π} (trans (ren-sem θ ρ h c df _)
                             (cong (⟦⟧ df) (split c (envˡ σ _ _) (envˡ σ Ψ₁ (Zero *ᵘ Ψ₂)) _ _ (envˡ-restrict σ _ _) (envˡ-restrict σ _ _) _ x)))
             (λ vf → refl)
    ren-sem θ ρ h c (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} {π₁ = π₁} {π₂ = π₂} df dx) x =
      bindCᵍ {π₁} (trans (ren-sem θ ρ h c df _)
                         (cong (⟦⟧ df) (split c (envˡ σ _ _) (envˡ σ Ψ₁ (One *ᵘ Ψ₂)) _ _ (envˡ-restrict σ _ _) (envˡ-restrict σ _ _) _ x)))
             (λ vf → bindCᵍ {π₂} {π} (trans (ren-sem θ ρ h c dx _)
                                       (cong (⟦⟧ dx) (split c (λ y → env*One σ _ (envʳ σ _ _ y)) (λ z → env*One σ Ψ₂ (envʳ σ Ψ₁ (One *ᵘ Ψ₂) z))
                                                          _ _ (env*One-envʳ-restrict σ _ _) (env*One-envʳ-restrict σ _ _) _ x)))
                              (λ vx → refl))
    ren-sem θ ρ h c (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} {π₁ = π₁} {π₂ = π₂} df dx) x =
      bindCᵍ {π₁} (trans (ren-sem θ ρ h c df _)
                         (cong (⟦⟧ df) (split c (envˡ σ _ _) (envˡ σ Ψ₁ (Many *ᵘ Ψ₂)) _ _ (envˡ-restrict σ _ _) (envˡ-restrict σ _ _) _ x)))
             (λ vf → bindCᵍ {π₂} {π} (trans (ren-sem θ ρ h c dx _)
                                       (cong (⟦⟧ dx) (split c (λ y → env*Many σ _ (envʳ σ _ _ y)) (λ z → env*Many σ Ψ₂ (envʳ σ Ψ₁ (Many *ᵘ Ψ₂) z))
                                                          _ _ (env*Many-envʳ-restrict σ _ _) (env*Many-envʳ-restrict σ _ _) _ x)))
                              (λ vx → refl))

    ren-sem θ ρ h c (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} d₁ d₂) x =
      trans (ren-sem (keep θ) _ _ (ckeep c) d₂ _)
            (cong (λ z → ⟦⟧ d₂ (z , tt)) (split c (envˡ σ _ _) (envˡ σ Ψ₂ (Zero *ᵘ Ψ₁)) _ _ (envˡ-restrict σ _ _) (envˡ-restrict σ _ _) _ x))
    ren-sem θ ρ h c (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π₁ = π₁} {π₂ = π₂} d₁ d₂) x =
      bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c d₁ _)
                             (cong (⟦⟧ d₁) (split c (λ y → env*One σ _ (envʳ σ _ _ y)) (λ z → env*One σ Ψ₁ (envʳ σ Ψ₂ (One *ᵘ Ψ₁) z))
                                                _ _ (env*One-envʳ-restrict σ _ _) (env*One-envʳ-restrict σ _ _) _ x)))
             (λ v → trans (ren-sem (keep θ) _ _ (ckeep c) d₂ _)
                          (cong (λ z → ⟦⟧ d₂ (z , v)) (split c (envˡ σ _ _) (envˡ σ Ψ₂ (One *ᵘ Ψ₁)) _ _ (envˡ-restrict σ _ _) (envˡ-restrict σ _ _) _ x)))
    ren-sem θ ρ h c (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π₁ = π₁} {π₂ = π₂} d₁ d₂) x =
      bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c d₁ _)
                             (cong (⟦⟧ d₁) (split c (λ y → env*Many σ _ (envʳ σ _ _ y)) (λ z → env*Many σ Ψ₁ (envʳ σ Ψ₂ (Many *ᵘ Ψ₁) z))
                                                _ _ (env*Many-envʳ-restrict σ _ _) (env*Many-envʳ-restrict σ _ _) _ x)))
             (λ v → trans (ren-sem (keep θ) _ _ (ckeep c) d₂ _)
                          (cong (λ z → ⟦⟧ d₂ (z , v)) (split c (envˡ σ _ _) (envˡ σ Ψ₂ (Many *ᵘ Ψ₁)) _ _ (envˡ-restrict σ _ _) (envˡ-restrict σ _ _) _ x)))

    ren-sem θ ρ h c ⊢unit x = refl

    ren-sem θ ρ h c (⊢pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π₁ = π₁} {π₂ = π₂} da db) x =
      bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c da _)
                             (cong (⟦⟧ da) (split c (envˡ σ _ _) (envˡ σ Ψ₁ Ψ₂) _ _ (envˡ-restrict σ _ _) (envˡ-restrict σ _ _) _ x)))
             (λ a → cong (SE.fmap π₂ _) (trans (ren-sem θ ρ h c db _)
                                               (cong (⟦⟧ db) (split c (envʳ σ _ _) (envʳ σ Ψ₁ Ψ₂) _ _ (envʳ-restrict σ _ _) (envʳ-restrict σ _ _) _ x))))
    ren-sem θ ρ h c (⊢fst {π = π} d) x = cong (SE.fmap π _) (ren-sem θ ρ h c d x)
    ren-sem θ ρ h c (⊢snd {π = π} d) x = cong (SE.fmap π _) (ren-sem θ ρ h c d x)
    ren-sem θ ρ h c (⊢inl {π = π} d) x = cong (SE.fmap π _) (ren-sem θ ρ h c d x)
    ren-sem θ ρ h c (⊢inr {π = π} d) x = cong (SE.fmap π _) (ren-sem θ ρ h c d x)
    ren-sem θ ρ h c (⊢case {Ψs = Ψs} {Ψ = Ψ} {qℓ = qℓ} {qr = qr} {π₁ = π₁} {π₂ = π₂} ds dl dr) x =
      bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c ds _)
                             (cong (⟦⟧ ds) (split c (envˡ σ _ _) (envˡ σ Ψs Ψ) _ _ (envˡ-restrict σ _ _) (envˡ-restrict σ _ _) _ x)))
             (λ { (inj₁ a) → trans (ren-sem (keep θ) _ _ (ckeep c) dl _)
                                   (cong (λ z → ⟦⟧ dl (z , slot qℓ a)) (split c (envʳ σ _ _) (envʳ σ Ψs Ψ) _ _ (envʳ-restrict σ _ _) (envʳ-restrict σ _ _) _ x))
                ; (inj₂ b) → trans (ren-sem (keep θ) _ _ (ckeep c) dr _)
                                   (cong (λ z → ⟦⟧ dr (z , slot qr b)) (split c (envʳ σ _ _) (envʳ σ Ψs Ψ) _ _ (envʳ-restrict σ _ _) (envʳ-restrict σ _ _) _ x)) })
    ren-sem θ ρ h c (⊢absurd {π = π} d) x = bindC {π} (ren-sem θ ρ h c d x) (λ _ → refl)
    ren-sem θ ρ h c (⊢roll {π = π} wf d) x = cong (SE.fmap π _) (ren-sem θ ρ h c d x)
    ren-sem θ ρ h c (⊢fold {Ψa = Ψa} {Ψt = Ψt} {π = π} {π₁ = π₁} {π₂ = π₂} wf da dt) x =
      bindCᵍ {π₁} (trans (ren-sem θ ρ h c da _)
                         (cong (⟦⟧ da) (split c (λ y → env*Many σ _ (envˡ σ _ _ y)) (λ z → env*Many σ Ψa (envˡ σ (Many *ᵘ Ψa) Ψt z))
                                            _ _ (env*Many-envˡ-restrict σ _ _) (env*Many-envˡ-restrict σ _ _) _ x)))
             (λ valg → bindCᵍ {π₂} {π} (trans (ren-sem θ ρ h c dt _)
                                         (cong (⟦⟧ dt) (split c (envʳ σ _ _) (envʳ σ (Many *ᵘ Ψa) Ψt) _ _ (envʳ-restrict σ _ _) (envʳ-restrict σ _ _) _ x)))
                                (λ _ → refl))
    ren-sem θ ρ h c (⊢unfold {Ψc = Ψc} {Ψs = Ψs} {π₁ = π₁} {π₂ = π₂} wf dc ds) x =
      bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c dc _)
                              (cong (⟦⟧ dc) (split c (λ y → env*Many σ _ (envˡ σ _ _ y)) (λ z → env*Many σ Ψc (envˡ σ (Many *ᵘ Ψc) Ψs z))
                                                 _ _ (env*Many-envˡ-restrict σ _ _) (env*Many-envˡ-restrict σ _ _) _ x)))
             (λ clo → cong (SE.fmap π₂ _) (trans (ren-sem θ ρ h c ds _)
                                                 (cong (⟦⟧ ds) (split c (envʳ σ _ _) (envʳ σ (Many *ᵘ Ψc) Ψs) _ _ (envʳ-restrict σ _ _) (envʳ-restrict σ _ _) _ x))))
    ren-sem θ ρ h c (⊢iter {Ψf = Ψf} {Ψs = Ψs} {π₁ = π₁} {π₂ = π₂} df ds) x =
      bindCᵍ {π₁} (trans (ren-sem θ ρ h c df _)
                         (cong (⟦⟧ df) (split c (λ y → env*Many σ _ (envˡ σ _ _ y)) (λ z → env*Many σ Ψf (envˡ σ (Many *ᵘ Ψf) Ψs z))
                                            _ _ (env*Many-envˡ-restrict σ _ _) (env*Many-envˡ-restrict σ _ _) _ x)))
             (λ f → bindCᵍ {π₂} {eff} (trans (ren-sem θ ρ h c ds _)
                                        (cong (⟦⟧ ds) (split c (envʳ σ _ _) (envʳ σ (Many *ᵘ Ψf) Ψs) _ _ (envʳ-restrict σ _ _) (envʳ-restrict σ _ _) _ x)))
                             (λ _ → refl))
    ren-sem θ ρ h c (⊢out {f = φ} {π₁ = π₁} wf d) x = bindCᵍ {π₁} {fin φ} (ren-sem θ ρ h c d x) (λ _ → refl)
    ren-sem θ ρ h c (⊢coerce {π = π} p d) x = cong (SE.fmap π _) (ren-sem θ ρ h c d x)
    ren-sem θ ρ h c ⊢lit-int x = refl
    ren-sem θ ρ h c ⊢lit-float x = refl
    ren-sem θ ρ h c (⊢prim {π = π} p d) x = cong (SE.fmap π _) (ren-sem θ ρ h c d x)
    ren-sem θ ρ h c (⊢sigop m) x = refl
    ren-sem θ ρ h c (⊢ref d τ rd) x = refl
    ren-sem θ ρ h c (⊢sub-eff g d) x = cong (SE.sub g) (ren-sem θ ρ h c d x)
    -- D276: sub-usaging is a restriction, and restriction commutes with thinning.
    ren-sem θ ρ h c (⊢sub-use p d) x = trans (ren-sem θ ρ h c d _) (cong (⟦⟧ d) (thin-restrict c p x))

    ------------------------------------------------------------------------
    -- Weakening by one unused variable (what the derived combinators use).
    ------------------------------------------------------------------------

    private
      wk-help : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Ty 0} {t π} (B : Ty 0) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
                  (w : Zero ∷ (idθ n θ* Ψ) ⊑ᵘ Zero ∷ Ψ) (x : Env σ (Γ ▸ B) (Zero ∷ Ψ))
              → ⟦⟧ (⊢sub-use {Γ = Γ ▸ B} w (ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip (cid Γ)) d)) x
                ≡ ⟦⟧ d (proj₁ x)
      wk-help {Γ = Γ} {Ψ} B d (0≤q ⊑∷ v) (x , tt) =
        trans (ren-sem _ _ _ (cskip (cid Γ)) d _) (cong (⟦⟧ d) (thin-id Γ Ψ v x))

    -- THE WEAKENING LEMMA: a term weakened by one unused variable means what it
    -- meant.
    wk-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Ty 0} {t π} (B : Ty 0) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
               (x : Env σ (Γ ▸ B) (Zero ∷ Ψ))
           → ⟦⟧ (wk-⊢ {B = B} d) x ≡ ⟦⟧ d (proj₁ x)
    wk-sem {Ψ = Ψ} B d x = wk-help B d (⊑ᵘ-≡ (cong (Zero ∷_) (θ*-id Ψ))) x
